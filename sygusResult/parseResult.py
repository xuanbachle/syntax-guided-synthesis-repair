import sys
import time
import logger
import sexp
import pprint
#from scipy import spatial
import math

parseOnly = False
simplify = False

def parseArguments(args):
    global parseOnly
    global simplify
    if not args:
        return
    option = args[0]

    if option == "-ipfile":
        global benchmarkFileName
        benchmarkFileName = args[1]
        parseArguments(args[2:])
    elif option == "-opfile":
        global outputFileName
        outputFileName = args[1]
        parseArguments(args[2:])
    elif option == "-extracted":
        global extractedDir
        extractedDir = args[1]
        parseArguments(args[2:])
    elif option == "-sygusfile":
        global sygusFileName
        sygusFileName = args[1]
        parseArguments(args[2:])
    elif option == "-solver":
        global solverName
        solverName = args[1]
        parseArguments(args[2:])
    elif option == "-log":
        global doLog
        doLog = True
        parseArguments(args[1:])
    elif option == "-parseOnly":
        parseOnly = True
        parseArguments(args[1:])
    elif option == "-simplify":
        simplify = True
        parseArguments(args[1:])
        #print ("GOT HERE: "+str(simplify)+str(args[1:]))
    else:
        print (option)
        print (args)
        raise Exception('Unknown command line option.')

def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'

def convertSyGusExp2CodeNorm(resExp, var2Change):
    op = ""
    if type(resExp) is list:
        if type(resExp[0]) is str:
            op = resExp[0]
        else:#for CVC4 output, e.g., ['BUILTIN', 'LEQ'] -> _BUILTIN_LEQ
            for e in resExp[0]:
                op = op+"_"+e+"_"

    elif type(resExp) is str:
        op = resExp
    else: #tuple e.g., ('Int', 1)
        op = str(resExp[1])
    #print("OP="+op)
    if isAnd(op):
        return "("+convertSyGusExp2CodeNorm(resExp[1], var2Change)+" && "+convertSyGusExp2CodeNorm(resExp[2], var2Change)+")"
    if isOr(op):
        return "(" + convertSyGusExp2CodeNorm(resExp[1], var2Change) + " || " + convertSyGusExp2CodeNorm(resExp[2], var2Change) + ")"
    elif isNot(op):
        return "(!"+convertSyGusExp2CodeNorm(resExp[1], var2Change)+")"
    elif isEq(op):
        return "(" + convertSyGusExp2CodeNorm(resExp[1], var2Change) + " == " + convertSyGusExp2CodeNorm(resExp[2], var2Change) + ")"
    elif isLeq(op):
        return "(" + convertSyGusExp2CodeNorm(resExp[1], var2Change) + " <= " + convertSyGusExp2CodeNorm(resExp[2], var2Change) + ")"
    elif isGeq(op):
        return "(" + convertSyGusExp2CodeNorm(resExp[1], var2Change) + " >= " + convertSyGusExp2CodeNorm(resExp[2], var2Change) + ")"
    elif isLessThan(op):
        return "(" + convertSyGusExp2CodeNorm(resExp[1], var2Change) + " < " + convertSyGusExp2CodeNorm(resExp[2], var2Change) + ")"
    elif isGreaterThan(op):
        return "(" + convertSyGusExp2CodeNorm(resExp[1], var2Change) + " > " + convertSyGusExp2CodeNorm(resExp[2], var2Change) + ")"
    elif isArithMinus(op):
        return "(" + convertSyGusExp2CodeNorm(resExp[1], var2Change) + " - " + convertSyGusExp2CodeNorm(resExp[2], var2Change) + ")"
    elif isArithPlus(op):
        return "(" + convertSyGusExp2CodeNorm(resExp[1], var2Change) + " + " + convertSyGusExp2CodeNorm(resExp[2], var2Change) + ")"
    elif isCVC4Const(op):
        #print("COonst "+op)
        return convertSyGusExp2CodeNorm(resExp[1], var2Change)
    else:
        if var2Change is None:
            return op
        else:
            correspondingVar = var2Change.get(op)
            if correspondingVar is None:
                return op
            else:
                return correspondingVar

def isAnd(e):
    if isinstance(e, str):
        return e == "and" or ("_AND_" in e)

    return False

def isOr(e):
    if isinstance(e, str):
        return e == "or" or ("_OR_" in e)

    return False

def isNot(e):
    if isinstance(e, str):
        return e == "not" or "_NOT_" in e

    return False

def isEq(e):
    if isinstance(e, str):
        return e == "=" or ("_EQUAL_" in e)
    return False

def isLeq(e):
    if isinstance(e, str):
        return e == "<=" or ("_LEQ_" in e)
    return False

def isGeq(e):
    if isinstance(e, str):
        return e == ">=" or ("_GEQ_" in e)
    return False

def isGreaterThan(e):
    if isinstance(e, str):
        return e == ">" or ("_GT_" in e)
    return False

def isLessThan(e):
    if isinstance(e, str):
        return e == "<" or ("_LT_" in e)
    return False

def isArithMinus(e):
    if isinstance(e, str):
        #TODO: add support CVC4
        return e == "-" or ("_MINUS_" in e)
    return False

def isArithPlus(e):
    if isinstance(e, str):
        #TODO: add support CVC4
        return e == "+" or ("_PLUS_" in e)
    return False


def isCVC4Const(e):
    #print e
    if isinstance(e, str):
        #TODO: add support CVC4
        return "CONST" in e
    return False

def cosine_similarity(v1,v2):
    "compute cosine similarity of v1 to v2: (v1 dot v2)/{||v1||*||v2||)"
    sumxx, sumxy, sumyy = 0, 0, 0
    for i in range(len(v1)):
        x = v1[i]; y = v2[i]
        sumxx += x*x
        sumyy += y*y
        sumxy += x*y
    return sumxy/math.sqrt(sumxx*sumyy)

def isSoDiff(vec1, vec2):
    #print "comparing"
    #print vec1
    #print vec2
    simScore = cosine_similarity(vec1, vec2)
    #print simScore
    #result = 1 - spatial.distance.cosine(vec1, vec2)
    #print "RES"
    #print (result)
    return simScore < 0.9

def isTrivialExpr(e, name, oldexpr):
    isConst = isConstantExpr(e)
    evec = exp2Vector(e, [0,0,0,0,0,0,0,0,0,0,0])
    oldVec = oldexpr.get(name)
    #print name
    #print oldVec
    tooDiff = isSoDiff(evec, oldVec)
    return isConst or tooDiff

def isConstantExpr(e):
    #constant in cvc4 form
    #print e
    if type(e) is list:
        if isCVC4Const(e[0]):
            return True
    #constant in other form
    if type(e) is not str and type(e) is not list:
        if len(e) > 1:
            if e[0] == 'Int' or e[0] == 'Bool':
                return True

    return False



def isIntOrBoolConst(s):
    try:
        int(s)
        return True
    except:
        return s == 'true' or s == 'false'


def expr2Str(resExp,var2Change,ext):
    #if isConstantExpr(e):
    #    if not isCVC4Const(e[0]):
    #        return str(e[1])
    #    else:
            #print str(e[1][1])
    #        return str(e[1][1])
    #else:
    op = ""
    if type(resExp) is list:
        if type(resExp[0]) is str:
            op = resExp[0]
        else:#for CVC4 output, e.g., ['BUILTIN', 'LEQ'] -> _BUILTIN_LEQ
            for e in resExp[0]:
                op = op+"_"+e+"_"

    elif type(resExp) is str:
        op = resExp
    else: #tuple e.g., ('Int', 1)
        op = str(resExp[1])
    #print("OP="+op)
    if isAnd(op):
        return "(and "+expr2Str(resExp[1], var2Change,ext)+" "+expr2Str(resExp[2], var2Change,ext)+")"
    if isOr(op):
        return "(or "+expr2Str(resExp[1], var2Change,ext)+" "+expr2Str(resExp[2],var2Change,ext)+")"
    elif isNot(op):
        return "(not "+expr2Str(resExp[1], var2Change,ext)+")"
    elif isEq(op):
        return "(= "+expr2Str(resExp[1],var2Change,ext)+" "+expr2Str(resExp[2],var2Change,ext)+")"
    elif isLeq(op):
        return "(<= "+expr2Str(resExp[1],var2Change,ext)+" "+expr2Str(resExp[2],var2Change,ext)+")"
    elif isGeq(op):
        return "(>= "+expr2Str(resExp[1],var2Change,ext)+" "+expr2Str(resExp[2],var2Change,ext)+")"
    elif isLessThan(op):
        return "(< "+expr2Str(resExp[1],var2Change,ext)+" "+expr2Str(resExp[2],var2Change,ext)+")"
    elif isGreaterThan(op):
        return "(> "+expr2Str(resExp[1],var2Change,ext)+" "+expr2Str(resExp[2],var2Change,ext)+")"
    elif isArithMinus(op):
        return "(- "+expr2Str(resExp[1],var2Change,ext)+" "+expr2Str(resExp[2],var2Change,ext)+")"
    elif isArithPlus(op):
        return "(+ "+expr2Str(resExp[1], var2Change,ext)+" "+expr2Str(resExp[2], var2Change,ext)+")"
    elif isCVC4Const(op):
        #print("COonst "+op)
        return expr2Str(resExp[1], var2Change,ext)
    else:
        if var2Change is None:
            if isIntOrBoolConst(op):
                return op
            else:
                return op+"_"+ext
        else:
            correspondingVar = var2Change.get(op)
            if correspondingVar is None:
                if isIntOrBoolConst(op):
                    return op
                else:
                    return op+"_"+ext
            else:
                return correspondingVar+"_"+ext

def extractDefFunSignature(funArgs, ext, varMap):
    res = ""
    for args in funArgs:
        if varMap is None:
            res += args[0]+"_"+ext+" "
        else:
            res += varMap.get(args[0])+"_"+ext+" "
        #print args[0]
    return res

def extractDefFunSignatureCVC4(funArgs, ext):
    res = ""
    for args in funArgs:
        res += str(args)+"_"+ext+" "
        #print args[0]
    return res

def exp2Vector(resExp, vector):
    #vector: and, or, not, =, <=, >=, <, >,+, -,*,/
    op = ""
    if type(resExp) is list:
        if type(resExp[0]) is str:
            op = resExp[0]
        else:#for CVC4 output, e.g., ['BUILTIN', 'LEQ'] -> _BUILTIN_LEQ
            for e in resExp[0]:
                op = op+"_"+e+"_"

    elif type(resExp) is str:
      op = resExp
    else: #tuple e.g., ('Int', 1)
      op = str(resExp[1])
      #print("OP="+op)
    if isAnd(op):
        vector[0] = vector[0]+5
        vector = exp2Vector(resExp[1], vector)
        return exp2Vector(resExp[2], vector)
    if isOr(op):
        vector[1] = vector[1]+5
        vector = exp2Vector(resExp[1], vector)
        return exp2Vector(resExp[2], vector)
    elif isNot(op):
        vector[2] = vector[2]+3
        return exp2Vector(resExp[1], vector)
    elif isEq(op):
        vector[3] = vector[3]+1
        vector = exp2Vector(resExp[1], vector)
        return exp2Vector(resExp[2], vector)
    elif isLeq(op):
        vector[4] = vector[4]+1
        vector = exp2Vector(resExp[1], vector)
        return exp2Vector(resExp[2], vector)
    elif isGeq(op):
        vector[5] = vector[5]+1
        vector = exp2Vector(resExp[1], vector)
        return exp2Vector(resExp[2], vector)
    elif isLessThan(op):
        vector[6] = vector[6]+1
        vector = exp2Vector(resExp[1], vector)
        return exp2Vector(resExp[2], vector)
    elif isGreaterThan(op):
        vector[7] = vector[7]+1
        vector = exp2Vector(resExp[1], vector)
        return exp2Vector(resExp[2], vector)
    elif isArithMinus(op):
        vector[8] = vector[8]+1
        vector = exp2Vector(resExp[1], vector)
        return exp2Vector(resExp[2], vector)
    elif isArithPlus(op):
        vector[9] = vector[9]+1
        vector = exp2Vector(resExp[1], vector)
        return exp2Vector(resExp[2], vector)
    else: #const and var
        #print ("OP="+op)
        #print vector
        #print vector[10]
        vector[10] = vector[10]+1
        #print vector[10]
        #print vector
        return vector

if __name__ == '__main__':
    if (len(sys.argv) < 2):
        print ('Usage: %s -file <Synth File> \n' % sys.argv[0])
        sys.exit(1)
    AppStartTime = time.clock()

    parseArguments(sys.argv[1:])

    try:
        benchmarkFile = open(benchmarkFileName)
    except:
        print ('No file found. Usage: %s -file <Synth File> \n' % sys.argv[0])

    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]

    #logger.SetLogging(doLog)

    #if logger.IsLogging():
    #    pprint.pprint(bmExpr)

    if parseOnly:
        for line in bmExpr:
            print line
    else:
        content = ""
        if solverName == "Stoc":
            funBodyDict={}
            funSignatureDict ={}
            for defFun in bmExpr:
                funBodyDict[defFun[1]] = defFun[-1]
                funSignatureDict[defFun[1]] = defFun[2]
            try:
                sygusFile = open(sygusFileName)
            except:
                print('No file found. Usage: %s -file <Synth File> \n' % sys.argv[0])
            sygus = stripComments(sygusFile)
            sygusExpr = sexp.sexp.parseString(sygus, parseAll=True).asList()[0]
            i = 0
            oldExprFileVec ={}
            for cmd in sygusExpr:
                if cmd[0] == 'synth-fun':
                    funName = cmd[1]
                    resBody = funBodyDict.get(funName)
                    resSig = funSignatureDict.get(funName)
                    sygusSig = cmd[2]
                    varMap = {} #res sig var -> sygus sig var
                    for index, eachSygusArg in enumerate(sygusSig):
                        varMap[resSig[index][0]] = eachSygusArg[0]
                    #content = convertSyGusExp2CodeNorm(resBody, varMap)
                    #print(funName+":"+content)
                    #--
                    if not simplify:
                         content = convertSyGusExp2CodeNorm(resBody, varMap)
                         print(funName+":"+content+":"+"OK")
                    else:
                         ext = funName.split("_")[1]
                         try:
                            oldExprFile = open(extractedDir+"/"+ext+".smt2")
                            oldExprStr = stripComments(oldExprFile)
                            oldExpr = sexp.sexp.parseString(oldExprStr, parseAll=True).asList()[0]
                            oldExprFileVec[ext]= exp2Vector(oldExpr[0][1], [0,0,0,0,0,0,0,0,0,0,0])
                         except:
                              print ('No file found. Usage: %s -file <Synth File> \n' % sys.argv[0])
                         if isTrivialExpr(resBody, ext, oldExprFileVec):
                            args = extractDefFunSignature(resSig, ext, varMap)
                            constraint = "(constraint (not (= ("+str(funName)+" "+args+") "+expr2Str(resBody, varMap, ext)+")))"
                            print (funName+":"+constraint+":"+"Trivial")
                         else:
                             content = convertSyGusExp2CodeNorm(resBody, varMap)
                             print(funName+":"+content+":"+"OK")
                    #--

        else:
            if not simplify:
                for defFun in bmExpr:
                    #pprint.pprint(defFun)
                    #pprint.pprint(defFun[-1])
                    content =convertSyGusExp2CodeNorm(defFun[-1], None)
                    # return ok without simplification
                    print (defFun[1]+":"+content+":"+"OK")
            else:
                #print oldExprFileExp
                oldExprFileVec ={}
                #for k,v in oldExprFileExp.iteritems():
                #    oldExprFileVec[k]=exp2Vector(v, [0,0,0,0,0,0,0,0,0,0,0])
                #print oldExprFileVec
                for defFun in bmExpr:
                    #pprint.pprint(defFun)
                    #pprint.pprint(defFun[-1])
                    #content =convertSyGusExp2CodeNorm(defFun[-1], None)
                    funName = defFun[1]
                    ext = funName.split("_")[1]
                    #oldExprFileExp = {}
                    try:
                        oldExprFile = open(extractedDir+"/"+ext+".smt2")
                        oldExprStr = stripComments(oldExprFile)
                        oldExpr = sexp.sexp.parseString(oldExprStr, parseAll=True).asList()[0]
                        oldExprFileVec[ext]= exp2Vector(oldExpr[0][1], [0,0,0,0,0,0,0,0,0,0,0])
                    except:
                        print ('No file found. Usage: %s -file <Synth File> \n' % sys.argv[0])
                    #print oldExprFileVec
                    if isTrivialExpr(defFun[-1],ext,oldExprFileVec):
                        args = ""
                        constraint = ""
                        content = defFun[-1]
                        if solverName == "CVC4":
                            #print defFun[2]
                            args = extractDefFunSignatureCVC4(defFun[2][1:], ext)
                            constraint = "(constraint (not (= ("+str(funName)+" "+args+") "+expr2Str(content, None, ext)+")))"
                        else:
                            #print defFun[2:len(defFun)-2][0]
                            args = extractDefFunSignature(defFun[2:len(defFun)-2][0], ext, None)
                            constraint = "(constraint (not (= ("+str(funName)+" "+args+") "+expr2Str(content, None, ext)+")))"

                        print (str(funName)+":"+constraint+":"+"Trivial")
                    else:
                        content =convertSyGusExp2CodeNorm(defFun[-1], None)
                        print (defFun[1]+":"+content+":"+"OK")

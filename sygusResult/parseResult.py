import sys
import time
import logger
import sexp
import pprint
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

def isTrivialExpr(e):
    return isConstantExpr(e)

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

def expr2Str(e):
    if isConstantExpr(e):
        if not isCVC4Const(e[0]):
            return str(e[1])
        else:
            #print str(e[1][1])
            return str(e[1][1])
    else:
        return str(e)

def extractDefFunSignature(funArgs, ext):
    res = ""
    for args in funArgs:
        res += args[0]+"_"+ext+" "
        #print args[0]
    return res

def extractDefFunSignatureCVC4(funArgs, ext):
    res = ""
    for args in funArgs:
        res += str(args)+"_"+ext+" "
        #print args[0]
    return res

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
                         if isTrivialExpr(resBody):
                            ext = funName.split("_")[1]
                            args = extractDefFunSignature(resSig, ext)
                            constraint = "(constraint (not (= ("+str(funName)+" "+args+") "+"("+expr2Str(resBody)+")"+")))"
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
                for defFun in bmExpr:
                    #pprint.pprint(defFun)
                    #pprint.pprint(defFun[-1])
                    #content =convertSyGusExp2CodeNorm(defFun[-1], None)
                    if isTrivialExpr(defFun[-1]):
                        args = ""
                        constraint = ""
                        funName = defFun[1]
                        ext = funName.split("_")[1]
                        content = defFun[-1]
                        if solverName == "CVC4":
                            #print defFun[2]
                            args = extractDefFunSignatureCVC4(defFun[2][1:], ext)
                            constraint = "(constraint (not (= ("+str(funName)+" "+args+") "+expr2Str(content)+")))"
                        else:
                            #print defFun[2:len(defFun)-2][0]
                            args = extractDefFunSignature(defFun[2:len(defFun)-2][0], ext)
                            constraint = "(constraint (not (= ("+str(funName)+" "+args+") "+"("+expr2Str(content)+")"+")))"

                        print (str(funName)+":"+constraint+":"+"Trivial")
                    else:
                        content =convertSyGusExp2CodeNorm(defFun[-1], None)
                        print (defFun[1]+":"+content+":"+"OK")

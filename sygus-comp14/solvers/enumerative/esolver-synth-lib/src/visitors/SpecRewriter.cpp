// SpecRewriter.cpp ---
//
// Filename: SpecRewriter.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:53:15 2014 (-0500)
//
//
// Copyright (c) 2013, Abhishek Udupa, University of Pennsylvania
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. All advertising materials mentioning features or use of this software
//    must display the following acknowledgement:
//    This product includes software developed by The University of Pennsylvania
// 4. Neither the name of the University of Pennsylvania nor the
//    names of its contributors may be used to endorse or promote products
//    derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
//

// Code:


#include "SpecRewriter.hpp"
#include "../solvers/ESolver.hpp"
#include "../descriptions/Operators.hpp"
#include "../expressions/UserExpression.hpp"
#include "Gatherers.hpp"

namespace ESolver {

SpecRewriter::SpecRewriter(ESolver* Solver, uint32 NumSynthFuncs)
        : ExpressionVisitorBase("SpecRewriter"),
          SynthFunArgOps((size_t)NumSynthFuncs),
          Solver(Solver),
          AuxIDCounter((uint64)0)
    {
        // Nothing here
    }

    SpecRewriter::~SpecRewriter()
    {
        // Nothing here
    }

    void SpecRewriter::VisitUserUQVarExpression(const UserUQVarExpression* Exp)
    {
        auto it = ExpMap.find(Exp);
        if (it == ExpMap.end()) {
            auto Op = Solver->CreateAuxVariable(AuxIDCounter++, Exp->GetType());
            auto AuxExp = Solver->CreateExpression(Op);
            AllAuxVarOps.push_back(Op);
            BaseAuxVarOps.insert(Op);
            ExpMap[Expression(Exp)] = AuxExp;
            RewriteStack.push_back(AuxExp);
        } else {
            RewriteStack.push_back(it->second);
        }
    }

    // For a synth fun, we need to ensure that arguments are
    // all aux vars (either base or derived)
    void SpecRewriter::VisitUserSynthFuncExpression(const UserSynthFuncExpression* Exp)
    {
        // Push through the children first.
        auto const& Children = Exp->GetChildren();
        const uint32 NumChildren = Children.size();
        for (auto const& Child : Children) {
            Child->Accept(this);
        }

        // The rewritten expressions are on the stack now,
        // we need to check if any of them is an expression
        // which needs to be computed. If so, we create an
        // aux var for the subexpression and set up an evaluation
        // rule
        // Gather the child expressions first
        vector<Expression> SubstChildren(Children.size());
        for (uint32 i = 0; i < NumChildren; ++i) {
            SubstChildren[Children.size() - i - 1] = RewriteStack.back();
            RewriteStack.pop_back();
        }

        vector<Expression> NewSubstChildren;
        vector<const AuxVarOperator*> CurArgOps;

        for (auto const& Child : SubstChildren) {
            if (Child->As<UserAuxVarExpression>() == nullptr) {
                // We need to fixup an eval rule for this child
                // Check if one already exists for it first
                auto it = ExpMap.find(Child);
                if (it != ExpMap.end()) {
                    NewSubstChildren.push_back(it->second);
                } else {
                    // Create a new aux var
                    auto Op = Solver->CreateAuxVariable(AuxIDCounter++, Child->GetType());
                    auto AuxExp = Solver->CreateExpression(Op);
                    ExpMap[Child] = AuxExp;
                    AllAuxVarOps.push_back(Op);

                    EvalRules.push_back(EvalRule(Op, Child));
                    NewSubstChildren.push_back(AuxExp);
                }
            } else {
                NewSubstChildren.push_back(Child);
            }

            auto NewSubstChild = NewSubstChildren.back()->As<UserAuxVarExpression>();
            CurArgOps.push_back(NewSubstChild->GetOp());
            BaseAuxVarOps.insert(NewSubstChild->GetOp());
        }


        // Create the expression with the substitutions
        auto NewExp = Solver->CreateExpression(Exp->GetOp(), NewSubstChildren);

        // Since this is a synth func expression,
        // we need to create an aux var for
        // ourselves and substitute the aux var for
        // ourself. But first check if there is already
        // a derived var available (CSE)
        auto it = ExpMap.find(Exp);
        if (it != ExpMap.end()) {
            // No need to create more derived vars
            RewriteStack.push_back(it->second);
        } else {
            auto Op = Solver->CreateAuxVariable(AuxIDCounter++, NewExp->GetType());
            auto AuxExp = Solver->CreateExpression(Op);
            ExpMap[Exp] = AuxExp;
            AllAuxVarOps.push_back(Op);
            EvalRules.push_back(EvalRule(Op, NewExp));
            RewriteStack.push_back(AuxExp);

            // Record that these aux vars are applied to update
            // the target aux var
            SynthFunArgOps[Exp->GetOp()->GetPosition()][CurArgOps] = Op;
        }
    }

    void SpecRewriter::VisitUserInterpretedFuncExpression(const UserInterpretedFuncExpression* Exp)
    {
        // Recurse on the children first
        auto const& Children = Exp->GetChildren();
        for (auto const& Child : Children) {
            Child->Accept(this);
        }

        // Make a new expression out of the rewritten expressions
        auto const NumChildren = Children.size();
        vector<Expression> NewChildren(NumChildren);

        for (uint32 i = 0; i < NumChildren; ++i) {
            NewChildren[NumChildren - i - 1] = RewriteStack.back();
            RewriteStack.pop_back();
        }

        auto NewExp = Solver->CreateExpression(Exp->GetOp(), NewChildren);
        RewriteStack.push_back(NewExp);
    }

    void SpecRewriter::VisitUserLetExpression(const UserLetExpression* Exp)
    {
        // We create an aux var for every let bound variable
        auto const& Bindings = Exp->GetLetBoundVars();

        for (auto const& Binding : Bindings) {
            Binding.second->Accept(this);
            auto RewrittenBinding = RewriteStack.back();
            RewriteStack.pop_back();

            auto Op = Solver->CreateAuxVariable(AuxIDCounter++, RewrittenBinding->GetType());
            auto AuxExp = Solver->CreateExpression(Op);
            AllAuxVarOps.push_back(Op);
            BaseAuxVarOps.insert(Op);
            ExpMap[Binding.first] = AuxExp;
            EvalRules.push_back(EvalRule(Op, RewrittenBinding));
        }

        // Finally, recurse on the expression
        Exp->GetBoundInExpression()->Accept(this);
    }

    void SpecRewriter::VisitUserLetBoundVarExpression(const UserLetBoundVarExpression* Exp)
    {
        auto it = ExpMap.find(Expression(Exp));
        // We must have our mapping in the ExpMap. That is our rewrite.
        if (it == ExpMap.end()) {
            throw InternalError((string)"Internal Error: Expected let bound variable " +
                                "to be already bound.\n" + "At: " + __FILE__ +
                                ":" + to_string(__LINE__));
        }

        RewriteStack.push_back(it->second);
        return;
    }

    void SpecRewriter::VisitUserConstExpression(const UserConstExpression* Exp)
    {
        // The rewrite of a constant is itself
        RewriteStack.push_back(Exp);
    }

    void SpecRewriter::VisitUserFormalParamExpression(const UserFormalParamExpression* Exp)
    {
        throw InternalError((string)"Internal Error: Did not expect to see " +
                            "a formal param expression.\n" + "At: " +
                            __FILE__ + ":" + to_string(__LINE__));
    }

    void SpecRewriter::VisitUserAuxVarExpression(const UserAuxVarExpression* Exp)
    {
        throw InternalError((string)"Internal Error: Did not expect to see an " +
                            " aux var expression.\n" + "At: " + __FILE__ + ":" +
                            to_string(__LINE__));
    }

    Expression SpecRewriter::Do(ESolver* Solver, const Expression& Exp,
                                vector<const AuxVarOperator*>& BaseAuxVarOps,
                                vector<const AuxVarOperator*>& DerivedAuxVarOps,
                                vector<map<vector<uint32>, uint32>>& SynthFunAppMaps)
    {
        auto&& SynthFuncs = SynthFuncGatherer::Do(Exp);
        const uint32 NumSynthFuncs = SynthFuncs.size();

        uint32 SynthFuncID = 0;
        for (auto const& SynthFunc : SynthFuncs) {
            SynthFunc->SetPosition(SynthFuncID++);
        }

        SpecRewriter Rewriter(Solver, NumSynthFuncs);
        Exp->Accept(&Rewriter);
        auto EvalRules = std::move(Rewriter.EvalRules);


        SynthFunAppMaps.clear();
        SynthFunAppMaps = vector<map<vector<uint32>, uint32>>((size_t)SynthFuncs.size());


        for (auto const& AuxOp : Rewriter.AllAuxVarOps) {
            if (Rewriter.BaseAuxVarOps.find(AuxOp) != Rewriter.BaseAuxVarOps.end()) {
                BaseAuxVarOps.push_back(AuxOp);
            } else {
                DerivedAuxVarOps.push_back(AuxOp);
            }
        }

        vector<map<vector<const AuxVarOperator*>, const AuxVarOperator*>> SynthFunArgOps;
        SynthFunArgOps = std::move(Rewriter.SynthFunArgOps);

        // Assign positions for base and derived aux vars
        uint32 AuxVarCounter = 0;
        for (auto const& BaseAV : BaseAuxVarOps) {
            BaseAV->SetPosition(AuxVarCounter++);
        }
        for (auto const& DerivedAV : DerivedAuxVarOps) {
            DerivedAV->SetPosition(AuxVarCounter++);
        }

        // Fixup the param maps in the eval rules
        for (auto const& Rule : EvalRules) {
            ParamMapFixup::Do(Rule.GetRHS());
        }

        for (uint32 i = 0; i < NumSynthFuncs; ++i) {
            const uint32 NumArgs = SynthFunArgOps[i].begin()->first.size();

            for (auto const& ArgOpsTargetOp : SynthFunArgOps[i]) {
                auto const& ArgOps = ArgOpsTargetOp.first;
                vector<uint32> CurMap((size_t)NumArgs, 0u);
                for (uint32 i = 0; i < NumArgs; ++i) {
                    CurMap[i] = ArgOps[i]->GetPosition();
                }
                SynthFunAppMaps[i][CurMap] = ArgOpsTargetOp.second->GetPosition();
            }
        }

        auto RewrittenConstraint = Rewriter.RewriteStack.back();
        auto Antecedent = Solver->CreateTrueExpression();
        for (auto const& EvalRule : EvalRules) {
            auto LHSVar = Solver->CreateExpression(EvalRule.GetLHS());

            Antecedent =
                Solver->CreateExpression("and", Antecedent,
                                         Solver->CreateExpression("=", EvalRule.GetRHS(),
                                                                  LHSVar));

        }
        return Solver->CreateExpression("=>", Antecedent, RewrittenConstraint);
    }

    ParamMapFixup::ParamMapFixup()
        : ExpressionVisitorBase("ParamMapFixup")
    {
        // Nothing here
    }

    ParamMapFixup::~ParamMapFixup()
    {
        // Nothing here
    }

    void ParamMapFixup::VisitUserSynthFuncExpression(const UserSynthFuncExpression* Exp)
    {
        auto const& Children = Exp->GetChildren();
        const uint32 NumChildren = Children.size();

        auto ParamMap = Exp->GetParamMap();
        for (uint32 i = 0; i < NumChildren; ++i) {
            auto const& Child = Children[i];
            auto Op = Child->GetOp()->As<AuxVarOperator>();
            if (Op == nullptr) {
                throw InternalError((string)"Internal Error: Expected to see an aux var.\n" +
                                    "At: " + __FILE__ + ":" + to_string(__LINE__));
            }
            ParamMap[i] = Op->GetPosition();
        }
    }

    void ParamMapFixup::Do(const Expression& Exp)
    {
        ParamMapFixup Fixup;
        Exp->Accept(&Fixup);
        return;
    }

} /* End namespace */


//
// SpecRewriter.cpp ends here

//===- unittests/Analysis/FlowSensitive/SingleVarConstantPropagation.cpp --===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines a simplistic version of Reaching Definitions
// TODO:
// 1. Currently only works for one variable (transfer wipes everything)
// 2. Only handles VarDecls, not assignments to already declared variables.
//===----------------------------------------------------------------------===//

#include "TestingSupport.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Analysis/CFG.h"
#include "clang/Analysis/FlowSensitive/DataflowAnalysis.h"
#include "clang/Analysis/FlowSensitive/DataflowEnvironment.h"
#include "clang/Analysis/FlowSensitive/DataflowLattice.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Testing/ADT/StringMapEntry.h"
#include "llvm/Testing/Support/Error.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include <optional>
#include <ostream>
#include <string>
#include "llvm/ADT/DenseMap.h"
#include <vector>
#include <iostream>


namespace clang {
namespace dataflow {
namespace {



static const FunctionDecl *getEnclosingFunction(const Stmt *S, ASTContext &Ctx) {
  DynTypedNode Node = DynTypedNode::create(*S);

  while (true) {
    auto Parents = Ctx.getParents(Node);
    if (Parents.empty())
      return nullptr;

    const DynTypedNode &Parent = Parents[0];
    if (const auto *FD = Parent.get<FunctionDecl>())
      return FD;

    Node = Parent;
  }
}

static unsigned getLineOffsetFromFunctionStart(const Stmt *S, ASTContext &Ctx) {
  const auto *FD = getEnclosingFunction(S, Ctx);
  assert(FD != nullptr);
  assert(FD->getBody() != nullptr);

  const SourceManager &SM = Ctx.getSourceManager();
  unsigned StmtLine = SM.getSpellingLineNumber(S->getBeginLoc());
  unsigned BodyLine = SM.getSpellingLineNumber(FD->getBody()->getBeginLoc());

  return StmtLine - BodyLine;
}

using namespace ast_matchers;



struct ReachingDefinitionsLattice {
  using StateType = llvm::DenseMap<const VarDecl*, std::vector<const Stmt*>>;

  // `std::nullopt` is "bottom".
  std::optional<StateType> Data;

  static ReachingDefinitionsLattice bottom() {
    return {std::nullopt};
  }
  // static constexpr ReachingDefinitionsLattice top() {
  //   return {VarValue{nullptr, 0}};
  // }

  friend bool operator==(const ReachingDefinitionsLattice &Lhs,
                         const ReachingDefinitionsLattice &Rhs) {
    return Lhs.Data == Rhs.Data;
  }

  LatticeJoinEffect join(const ReachingDefinitionsLattice &Other) {

    /// TODO: For ever VarDecl in the lattice, compute vector difference between this.Data[var] and Other.Data[var]. 
    // If the result is non-empty, add the Stmts in the result to this.Data[var] and mark a changed flag to return 
    // LatticeJoinEffect::Changed. If nothing changes, return LatticeJoinEffect::Unchanged.

    if (!Other.Data.has_value())
      return LatticeJoinEffect::Unchanged;

    if (!Data.has_value()) {
      Data = *Other.Data;
      return LatticeJoinEffect::Changed;
    }

    auto &OtherData = *(Other.Data);

    bool Changed = false;

    for (auto& entry : *Data) {
      const VarDecl *VD = entry.first;
      auto &ThisStmts = entry.second;
      auto It = OtherData.find(VD);
      std::vector<const Stmt*> OtherStmts;
      if (It != OtherData.end()) {
          OtherStmts = It->second;
      }
      if (OtherStmts.empty()) {
          continue;
      }
      std::vector<const Stmt*> result;
      std::set_difference(
          ThisStmts.begin(), ThisStmts.end(),
          OtherStmts.begin(), OtherStmts.end(),
          std::back_inserter(result)
      );

      for (const Stmt *S : result) {
          ThisStmts.push_back(S);
          Changed = true;
      }
    }

    auto effect = Changed ? LatticeJoinEffect::Changed : LatticeJoinEffect::Unchanged;
    return effect;
   
}};


std::ostream &operator<<(std::ostream &OS,
                         const ReachingDefinitionsLattice &L) {
  if (!L.Data.has_value()) {
    return OS <<  "None";
  }
  for (const auto &Entry : *L.Data) {
    const VarDecl *VD = Entry.first;
    OS << VD->getName().str() << " defined at lines: ";
    for (const Stmt *S : Entry.second) {
      OS << getLineOffsetFromFunctionStart(S, VD->getASTContext()) << " ";
    }
    OS << "\n";
  }
  return OS;
}

} // namespace

static constexpr char kVar[] = "var";


namespace {
// N.B. This analysis is deliberately simplistic, leaving out many important
// details needed for a real analysis in production. Most notably, the transfer
// function does not account for the variable's address possibly escaping, which
// would invalidate the analysis.
class ReachingDefsAnalysis
    : public DataflowAnalysis<ReachingDefsAnalysis,
                              ReachingDefinitionsLattice> {
public:
  explicit ReachingDefsAnalysis(ASTContext &Context)
      : DataflowAnalysis<ReachingDefsAnalysis,
                         ReachingDefinitionsLattice>(Context) {}

  static ReachingDefinitionsLattice initialElement() {
    return ReachingDefinitionsLattice::bottom();
  }

  void transfer(const CFGElement &E, ReachingDefinitionsLattice &Element,
                Environment &Env) {
    auto CS = E.getAs<CFGStmt>();
    if (!CS) return;
    const Stmt* S = CS->getStmt();
    auto matcher = stmt(
        declStmt(hasSingleDecl(varDecl(   
                                                ).bind(kVar)))
                                      );

    ASTContext &Context = getASTContext();
    auto Results = match(matcher, *S, Context);
    if (Results.empty())
      return;
    assert(Results.size() == 1);
    const BoundNodes &Nodes = Results[0];

    const auto *Var = Nodes.getNodeAs<clang::VarDecl>(kVar);
    assert(Var != nullptr);
    
    // If we found an assignment to the variable, all previous definitions of the variable are killed, so we replace them with the new definition.
    Element.Data = ReachingDefinitionsLattice::StateType();
    (*Element.Data)[Var] = {S};
  }
};

using ::clang::dataflow::test::AnalysisInputs;
using ::clang::dataflow::test::AnalysisOutputs;
using ::clang::dataflow::test::checkDataflow;
using ::llvm::IsStringMapEntry;
using ::testing::UnorderedElementsAre;




MATCHER_P2(
    HoldsCPLattice, VarName, ExpectedOffsets,
    ((negation ? "doesn't hold" : "holds") +
     llvm::StringRef(" reaching definitions for variable '") +
     llvm::StringRef(VarName) + "'")
        .str()) {
  const auto &Lattice = arg.Lattice;
  if (!Lattice.Data)
    return false;

  const auto &State = *Lattice.Data;

  const VarDecl *MatchedVar = nullptr;
  for (const auto &Entry : State) {
    const VarDecl *VD = Entry.first;
    if (VD != nullptr && VD->getName() == VarName) {
      MatchedVar = VD;
      break;
    }
  }

  if (MatchedVar == nullptr)
    return false;

  auto It = State.find(MatchedVar);
  if (It == State.end())
    return false;

  ASTContext &Ctx = MatchedVar->getASTContext();

  std::vector<unsigned> ActualOffsets;
  for (const Stmt *DefStmt : It->second)
    ActualOffsets.push_back(getLineOffsetFromFunctionStart(DefStmt, Ctx));

  std::sort(ActualOffsets.begin(), ActualOffsets.end());

  std::vector<unsigned> Expected(ExpectedOffsets.begin(), ExpectedOffsets.end());
  std::sort(Expected.begin(), Expected.end());

  return ExplainMatchResult(::testing::ContainerEq(Expected), ActualOffsets,
                            result_listener);
}



template <typename Matcher>
void RunDataflow(llvm::StringRef Code, Matcher Expectations) {
  ASSERT_THAT_ERROR(
      checkDataflow<ReachingDefsAnalysis>(
          AnalysisInputs<ReachingDefsAnalysis>(
              Code, hasName("fun"),
              [](ASTContext &C, Environment &) {
                return ReachingDefsAnalysis(C);
              })
              .withASTBuildArgs({"-fsyntax-only", "-std=c++17"}),
          /*VerifyResults=*/
          [&Expectations](const llvm::StringMap<DataflowAnalysisState<
                              ReachingDefsAnalysis::Lattice>> &Results,
                          const AnalysisOutputs &) {
            EXPECT_THAT(Results, Expectations);
          }),
      llvm::Succeeded());
}

TEST(ReachingDefsTest, Trivial) {
  std::string Code = R"(
    void fun() {
      int target = 1;
      // [[p]]
    }
  )";
  RunDataflow(Code,
              UnorderedElementsAre(
                IsStringMapEntry("p", HoldsCPLattice("target", std::vector<unsigned>{1})))
              );
}


TEST(ReachingDefsTest, OneVar) {
  std::string Code = R"(
    void fun(int x) {
      if (x < 0) {
        int target = 1;
        // [[p1]]
      } else {
        int target = 2;
        // [[p2]]
      }
    }
  )";
  RunDataflow(Code,
              UnorderedElementsAre(
                IsStringMapEntry("p1", HoldsCPLattice("target", std::vector<unsigned>{2})),
                IsStringMapEntry("p2", HoldsCPLattice("target", std::vector<unsigned>{5}))
              ));
}

// TEST(ReachingDefsTest, TwoVars) {
//   std::string Code = R"(
//     void fun(int x) {
//       if (x < 0) {
//         int v1 = 1;
//         int v2 = 2;
//         // [[p1]]
//       } else {
//         int v1 = 10;
//         // [[p2]]
//       }
//     }
//   )";
//   RunDataflow(Code,
//               UnorderedElementsAre(
//                 IsStringMapEntry("p1", HoldsCPLattice("v1", std::vector<unsigned>{2})),
//                 IsStringMapEntry("p1", HoldsCPLattice("v2", std::vector<unsigned>{3})),
//                 IsStringMapEntry("p2", HoldsCPLattice("v1", std::vector<unsigned>{6}))
//               ));
// }

} // namespace
} // namespace dataflow
} // namespace clang

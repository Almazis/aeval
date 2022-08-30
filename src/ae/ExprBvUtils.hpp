#ifndef EXPRBVSIMPL__HPP__
#define EXPRBVSIMPL__HPP__
#include "ufo/Smt/EZ3.hh"
#include "ufo/ExprBv.hh"

namespace ufo
{
  unsigned getBvSize(Expr exp);
  Expr rewriteSignedCmp(Expr exp);
  void getSignedCmps (Expr a, ExprVector &scmps);
//  Expr rewriteDivisible(Expr exp);
//  Expr rewriteRem(Expr exp);
  Expr reBuildBvNegCmp(Expr fla, Expr lhs, Expr rhs);

  Expr bvAdditiveInverse(Expr e);
  void getBaddTerm (Expr a, ExprVector &terms);
  Expr bvReBuildCmp(Expr exp, Expr lhs, Expr rhs);
  bool isBmulVar(Expr e, Expr var);
}
#endif


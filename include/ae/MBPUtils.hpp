#ifndef MBPUTILS__HPP__
#define MBPUTILS__HPP__

#include "ae/AeValSolver.hpp"

namespace ufo {
  Expr mixQE(Expr s, Expr constVar, ExprMap &substsMap, ZSolver<EZ3>::Model &m);
  Expr mixQE(Expr s, Expr constVar, ExprMap &substsMap, ZSolver<EZ3>::Model &m,
              SMTUtils &u, int debug);
  Expr createQuantifiedFormulaRestr(Expr def, Expr a, bool forall = false);
  Expr createQuantifiedFormulaRestr (Expr def, ExprSet& vars, bool forall = false);
}

#endif
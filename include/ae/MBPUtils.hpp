#ifndef MBPUTILS__HPP__
#define MBPUTILS__HPP__

#include "ae/AeValSolver.hpp"

namespace ufo {
  Expr mixQE(Expr s, Expr constVar, ExprMap &substsMap, ZSolver<EZ3>::Model &m);
}

#endif
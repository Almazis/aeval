#ifndef MBPUTILS__HPP__
#define MBPUTILS__HPP__

#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"

namespace ufo {
  

  enum laType {
    REALTYPE = 0,
    INTTYPE,
    MIXTYPE,
    NOTYPE
  };



  class MBPUtils 
  {
    Expr eVar;
    ZSolver<EZ3>::Model &m;
    ExprFactory &efac;
    SMTUtils &u;

    int intOrReal(Expr s);
    void laMergeBounds(ExprVector &loVec, ExprVector &upVec, ExprSet &outSet,
                        ZSolver<EZ3>::Model &m, Expr coef = NULL);
    Expr lraMultTrans(Expr t);
    Expr realQE(ExprSet sSet);
    Expr divTransHelper(Expr t);
    Expr divMultTransInt(Expr t);
    Expr vecElemInitInt(Expr t);
    Expr vecElemInitBv(Expr t);
    Expr coefApply(Expr t, int LCM);
    Expr coefApplyBv(Expr t, int LCM);
    int coefTrans(ExprVector &sVec);
    bvMultCoef coefTransBv(ExprVector &sVec);
    
    Expr intQE(ExprSet sSet);
    void ineqPrepare(Expr t, ExprSet &);
    Expr bvQE(ExprSet sSet);


  public:
    MBPUtils(Expr _var, ZSolver<EZ3>::Model& _m, SMTUtils& _u) : 
      eVar(_var), m(_m), efac(eVar->getFactory()), u(_u) {}
    Expr mixQE(Expr s, int debug);

  };
}

#endif
#include <cmath>
#include "ae/MBPUtils.hpp"
#include "common.h"
#include "ae/BvNormalization.hpp"

using namespace ufo;

/**
 * intOrReal - checks expression type
 */
int MBPUtils::intOrReal(Expr s)
{
  ExprVector sVec;
  bool realType = false, intType = false;
  filter(s, bind::IsNumber(), back_inserter(sVec));
  filter(s, bind::IsConst(), back_inserter(sVec));
  for(auto ite : sVec)
  {
    if(bind::isIntConst(ite) || isOpX<MPZ>(ite))
      intType = true;
    else if(bind::isRealConst(ite) || isOpX<MPQ>(ite))
      realType = true;
    else
      assert(false); // Error identifying
  }

  if(realType && intType)
    return MIXTYPE; // a bad case
  else if(realType)
    return REALTYPE;
  else if(intType)
    return INTTYPE;
  else
    return NOTYPE; // t == true
}

/**
 * laMergeBounds - merges lower and upper bounds
 * 
 * @loVec: lower bounds (y >= l, y > l), changed within function
 * @upVec: upper bounds (y <= u, y < u), changed within function
 * @outSet: output, a set of inequalities, which do not not contain y
 * @m: Z3 model, must passed as param for lambda function 
 * @coef: coefitient in front of y for LIA with multiplication constraints
 *        in LRA case equal to NULL
 */
void MBPUtils::laMergeBounds(
  ExprVector &loVec,
  ExprVector &upVec,
  ExprSet &outSet,
  ZSolver<EZ3>::Model &m,
  Expr coef)
{
  if(upVec.empty() || loVec.empty())
    return;

  std::sort(loVec.begin(), loVec.end(), [&m](Expr a, Expr b) {
    Expr ra = a->right(), rb = b->right();
    if(isOpX<TRUE>(m.eval(mk<EQ>(ra, rb)))) {
      if(isOpX<GEQ>(b))
        return true;
      return false;
    }
    return isOpX<TRUE>(m.eval(mk<LT>(ra, rb)));
  });

  std::sort(upVec.begin(), upVec.end(), [&m](Expr a, Expr b) {
    Expr ra = a->right(), rb = b->right();
    if(isOpX<TRUE>(m.eval(mk<EQ>(ra, rb)))) {
      if(isOpX<LEQ>(b))
        return false;
      return true;
    }
    return isOpX<TRUE>(m.eval(mk<LT>(ra, rb)));
  });

  Expr loBound = loVec.back();
  Expr upBound = upVec.front();

  if(coef != NULL)
  { // integers with multiplication case
    outSet.insert(mk<LT>(
      mk<IDIV>(loBound->right(), coef), mk<IDIV>(upBound->right(), coef)));
  }
  else if(isOpX<GEQ>(loBound) && isOpX<LEQ>(upBound))
    outSet.insert(mk<LEQ>(loBound->right(), upBound->right()));
  else
    outSet.insert(mk<LT>(loBound->right(), upBound->right()));

  for(auto ite = upVec.begin() + 1; ite != upVec.end(); ite++)
    outSet.insert(mk<LEQ>(upBound->right(), (*ite)->right()));
  for(auto ite = loVec.begin(); ite != loVec.end() - 1; ite++)
    outSet.insert(mk<LEQ>((*ite)->right(), loBound->right()));
}

/**
 * lraMultTrans - normalize inequality in LRA through dividing both sides
 */
Expr MBPUtils::lraMultTrans(Expr t)
{
  Expr lhs = t->left(), rhs = t->right();
  while(isOp<MULT>(lhs)) //until lhs is no longer *
  {
    Expr lOperand = lhs->left(), rOperand = lhs->right();
    bool yOnTheLeft = contains(lOperand, eVar);

    rhs = mk<DIV>(rhs, yOnTheLeft ? rOperand : lOperand);
    lhs = yOnTheLeft ? lOperand : rOperand;
    if (!contains(lhs, eVar))
      unreachable();
  }
  return (mk(t->op(), lhs, rhs));
}


/**
 * vecElemInitInt - removes LT and GEQ, gathers multipliers to one coef
 */
Expr MBPUtils::vecElemInitBv(Expr t)
{
  // get rid of LT and GEQ
  // if(isOpX<BULT>(t))
  //   t = bultToBule(t, m);
  // else if(isOpX<BUGE>(t))
  //   t = bugeToBugt(t, m);
  return t;
}

/**
 * coefApplyBv -  helper for coefTransBv, equalizes coeficient with respect to LCM
 */
Expr MBPUtils::coefApplyBv(Expr t, int LCM)
{
  int bvSize = getBvSize(eVar);
  Expr lhs = t->left(), rhs = t->right();
  Expr newCoef = bv::bvnum(LCM, bvSize, efac);
  if(isBmulVar(lhs, eVar))
  {
    Expr origCoef = getBmulVar(lhs, eVar);
    int coef = boost::lexical_cast<int>(origCoef->left());
    Expr rhsCoef = bv::bvnum(LCM/coef, bvSize, efac);
    rhs = mk<BMUL>(rhsCoef, rhs);
  }
  else
    rhs = mk<BMUL>(newCoef, rhs);
  lhs = mk<BMUL>(newCoef, eVar);
  return (mk(t->op(), lhs, rhs));
}

/**
 * coefTransBv - handles multiplication, collects and equalizes coeficients
 * 
 * @sVec: input inequalities, not changed within function 
 * @return struct of int and bool: int is LCM of the coeficients, bool is overflow identificator
 */
bvMultCoef MBPUtils::coefTransBv(ExprVector &sVec)
{
  ExprVector outVec;
  int LCM = 1;
  set<int> multipliers;
  // Gather LCM
  for(auto ite = sVec.begin(); ite != sVec.end(); ite++)
  {
    Expr lhs = (*ite)->left();
    if(isBmulVar(lhs, eVar)) {
      Expr coef = getBmulVar(lhs, eVar);
      multipliers.insert(boost::lexical_cast<int>(coef->left()));
    }
  }
  for(auto i : multipliers)
    LCM = boost::lcm(LCM, i);

  int bvSize = getBvSize(eVar);
  int maxVal = pow(2, bvSize) - 1;
  
  if (LCM > maxVal)
    return {0, true};
  else if(LCM > 1)
    for(auto ite = sVec.begin(); ite != sVec.end(); ite++)
      *ite = coefApplyBv(*ite, LCM);
  return {LCM, false};
}


/**
 * bvQE - MBP procedure for bitvector arithmetics
 * @sSet: set of inequalities, not normalized
 */
Expr MBPUtils::bvQE(ExprSet sSet)
{
  normalizator n(eVar, m);
  ExprSet normalizedSet;
  for (auto e : sSet) {
    bool success = n.normalize(e, normalizedSet);
    if (!success)
      normalizedSet.insert(replaceAll(e, eVar, m.eval(eVar)));
  }

  // filter out everything with no eVar
  ExprVector borders;
  for (auto ne : normalizedSet) {
    if (contains(ne, eVar)) {
      Expr initEx = vecElemInitBv(ne);
      borders.push_back(initEx);
      normalizedSet.erase(ne);
    }
  }

  coefTransBv(borders);

  // merge borders 

  return conjoin(normalizedSet, efac); // dummy
}

/**
 * realQE - MBP procedure for LRA
 * @sSet: set of inequalities with eVar on lhs
 */
Expr MBPUtils::realQE(ExprSet sSet)
{
  ExprVector sVec, upVec, loVec;

  for(auto t : sSet)
  {
    if(isOp<MULT>(t->left()))
      t = lraMultTrans(t);
    sVec.push_back(t);
  }
  // Collecting upper & lower bound
  for(auto ite = sVec.begin(); ite != sVec.end(); ite++)
  {
    if(isOpX<GT>(*ite) || isOpX<GEQ>(*ite))
      loVec.push_back(*ite);
    else if(isOpX<LT>(*ite) || isOpX<LEQ>(*ite))
      upVec.push_back(*ite);
  }

  ExprSet outSet;
  laMergeBounds(loVec, upVec, outSet, m);

  return conjoin(outSet, efac);
}

/**
 * divTransHelper - eliminates division from lhs once 
 */
Expr MBPUtils::divTransHelper(Expr t)
{
  if(!isOpX<GT>(t) && !isOpX<LEQ>(t))
    unreachable();
  
  Expr lhs = t->left(), rhs = t->right();
  Expr one = mkTerm(mpz_class(1), efac);
  Expr y, coef;

  if(contains(lhs->left(), eVar))
    y = lhs->left(), coef = lhs->right();
  else
    assert(false);
  return mk(t->op(), y, mk<MINUS>(mk<MULT>(mk<PLUS>(rhs, one), coef), one));
}

/**
 * divMultTransInt - calculate coef recursively, eliminate division
 */
Expr MBPUtils::divMultTransInt(Expr t)
{
  Expr lhs = t->left(), rhs = t->right();
  if (!isOp<MULT>(lhs) && !isOp<IDIV>(lhs))
    return t;
  if (lhs->arity() != 2)
    return t;

  int coef = 1;
  while(lhs->arity() != 1)
  {
    if(isOpX<MULT>(lhs))
    {
      if(isOpX<MPZ>(lhs->left()))
      {
        coef *= boost::lexical_cast<int>(lhs->left());
        t = mk(t->op(), lhs->right(), rhs);
      }
      else if(isOpX<MPZ>(lhs->right()))
      {
        coef *= boost::lexical_cast<int>(lhs->right());
        t = mk(t->op(), lhs->left(), rhs);
      }
      else
      {
        // contains coefficient that's not a integer constant
        assert(false); //critical Error
      }
    }
    else if(isOpX<IDIV>(lhs))
      t = divTransHelper(t);
    else
      notImplemented(); // Unexpected operation (not idiv or mult)

    lhs = t->left(), rhs = t->right();
  }

  if(coef > 1)
    return mk(
      t->op(), mk<MULT>(mkTerm(mpz_class(coef), t->getFactory()), lhs), rhs);
  else
    return mk(t->op(), lhs, rhs);
}

/**
 * vecElemInitInt - removes LT and GEQ, gathers multipliers to one coef
 */
Expr MBPUtils::vecElemInitInt(Expr t)
{
  Expr lhs = t->left(), rhs = t->right();

  // get rid of LT and GEQ
  Expr constOne = mkTerm(mpz_class(1), efac);
  if(isOpX<LT>(t))
    t = mk<LEQ>(lhs, mk<MINUS>(rhs, constOne));
  else if(isOpX<GEQ>(t))
    t = mk<GT>(lhs, mk<MINUS>(rhs, constOne));

  t = divMultTransInt(t);

  return t;
}

/**
 * coefApply -  helper for coefTrans, equalizes coeficient with respect to LCM
 */
Expr MBPUtils::coefApply(Expr t, int LCM)
{
  Expr lhs = t->left(), rhs = t->right();
  Expr newCoef = mkTerm(mpz_class(LCM), efac);
  if(isOp<MULT>(lhs))
  {
    Expr origCoef = (isOpX<MPZ>(lhs->left())) ? lhs->left() : lhs->right();
    Expr rhsCoef = mkTerm(
      mpz_class(LCM / boost::lexical_cast<int>(origCoef)), efac);
    rhs = mk<MULT>(rhsCoef, rhs);
  }
  else
    rhs = mk<MULT>(newCoef, rhs);
  lhs = mk<MULT>(newCoef, eVar);
  return (mk(t->op(), lhs, rhs));
}

/**
 * coefTrans - handles multiplication, collects and equalizes coeficients
 * 
 * @sVec: input inequalities, not changed within function 
 * @return int: LCM of the coeficients
 */
int MBPUtils::coefTrans(ExprVector &sVec)
{
  ExprVector outVec;
  int LCM = 1;
  set<int> multipliers;
  // Gather LCM
  for(auto ite = sVec.begin(); ite != sVec.end(); ite++)
  {
    Expr lhs = (*ite)->left();
    if(isOp<MULT>(lhs))
    {
      Expr coef = (isOpX<MPZ>(lhs->left())) ? lhs->left() : lhs->right();
      multipliers.insert(boost::lexical_cast<int>(*coef));
    }
  }
  for(auto i : multipliers)
    LCM = boost::lcm(LCM, i);

  if(LCM > 1)
    for(auto ite = sVec.begin(); ite != sVec.end(); ite++)
      *ite = coefApply(*ite, LCM);
  return LCM;
}

/**
 * intQE - MBP procedure for LIA
 * @sSet: set of inequalities with eVar on lhs
 */
Expr MBPUtils::intQE(ExprSet sSet)
{
  Expr coefExpr = NULL;
  ExprSet outSet;
  ExprVector sVec, loVec, upVec;
  /* Transformation Stage */
  for(auto t : sSet)
  {
    Expr initEx = vecElemInitInt(t);
    sVec.push_back(initEx);
  }
  // Coefficient Transformation, and extract the coefficient.
  int coef = coefTrans(sVec);
  if(coef > 1)
    coefExpr = mkTerm(mpz_class(coef), efac);
  // Collecting upper & lower bound
  for(auto ite = sVec.begin(); ite != sVec.end(); ite++)
  {
    if(isOpX<GT>(*ite))
      loVec.push_back(*ite);
    else if(isOpX<LEQ>(*ite))
      upVec.push_back(*ite);
  }
  laMergeBounds(loVec, upVec, outSet, m, coefExpr);

  return conjoin(outSet, efac);
}

/**
 * ineqPrepare - helper for mixQE, rewrites ineq and checks type consistency  
 */
void MBPUtils::ineqPrepare(Expr t, ExprSet &sameTypeSet)
{
  if(isOpX<NEG>(t) && isOp<ComparissonOp>(t->left()))
    t = mkNeg(t->left());
  if(isOp<ComparissonOp>(t))
  {
    // rewrite so that y is on lhs, with positive coef
    t = simplifyArithm(reBuildCmp(
      t,
      mk<PLUS>(t->arg(0), additiveInverse(t->arg(1))),
      mkMPZ(0, eVar->efac())));
    t = ineqSimplifier(eVar, t);

    int intVSreal = intOrReal(t);
    if(isReal(eVar) && (intVSreal == REALTYPE))
      sameTypeSet.insert(t);
    else if(isInt(eVar) && (intVSreal == INTTYPE))
      sameTypeSet.insert(t);
    else if(intVSreal != NOTYPE)
      notImplemented(); // MIXTYPE not supported
  }
  else if (isOp<BvUCmp>(t))
  {
    if (!isBvArith(t))
      sameTypeSet.insert(replaceAll(t, eVar, m.eval(eVar)));
    else if (isOpX<BULT>(t))
      bultToBule(t, m, sameTypeSet);
    else if (isOpX<BUGT>(t))
      bugtToBuge(t, m, sameTypeSet);
    else
      sameTypeSet.insert(t);
  }
  else
    unreachable();
}

Expr MBPUtils::mixQE(Expr s, int debug)
{
  Expr output;
  ExprSet outSet, temp;
  if(eVar == NULL)
    return s; // nothing to eliminate

  // Boolean case.
  if(isBoolean(eVar)) {
    output = simplifyBool(mk<OR>(
      replaceAll(s, eVar, mk<TRUE>(s->efac())),
      replaceAll(s, eVar, mk<FALSE>(s->efac()))));
    return output;
  }

  getConj(s, temp);
  ExprSet sameTypeSet;
  for(auto t : temp)
  {
    if (t == NULL)
      continue;
    if(!contains(t, eVar)) {
      outSet.insert(t);
      continue;
    }
    // rewrite and check type, put output in sameTypeSet
    ineqPrepare(t, sameTypeSet);
  }

  if(!sameTypeSet.empty())
    outSet.insert(isBv(eVar) ? bvQE(sameTypeSet) :
                  isReal(eVar) ? realQE(sameTypeSet) :
                  intQE(sameTypeSet));

  return conjoin(outSet, efac);
}
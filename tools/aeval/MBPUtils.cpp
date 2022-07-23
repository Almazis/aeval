#include "ae/MBPUtils.hpp"

#include "ae/AeValSolver.hpp"
#include "common.h"

using namespace ufo;

int intOrReal(Expr s)
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
    return MIXTYPE;
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
 * @m: Z3 model, passed as param for lambda function 
 * @coef: coefitient in front of y for LIA with multiplication constraints
 */
void laMergeBounds(
  ExprVector &loVec,
  ExprVector &upVec,
  ExprSet &outSet,
  ZSolver<EZ3>::Model &m,
  Expr coef = NULL)
{
  if(upVec.empty() || loVec.empty())
    return;

  std::sort(loVec.begin(), loVec.end(), [&m](Expr a, Expr b) {
    Expr ra = a->right();
    Expr rb = b->right();
    if(isOpX<TRUE>(m.eval(mk<EQ>(ra, rb))))
    {
      if(isOpX<GEQ>(b))
        return true;
      return false;
    }
    return isOpX<TRUE>(m.eval(mk<LT>(ra, rb)));
  });

  std::sort(upVec.begin(), upVec.end(), [&m](Expr a, Expr b) {
    Expr ra = a->right();
    Expr rb = b->right();
    if(isOpX<TRUE>(m.eval(mk<EQ>(ra, rb))))
    {
      if(isOpX<LEQ>(b))
        return false;
      return true;
    }
    return isOpX<TRUE>(m.eval(mk<LT>(ra, rb)));
  });

  // outs() << "upVec: ";
  // for(auto ite = upVec.begin(); ite != upVec.end(); ite++)
  //     outs() << *ite << " ";
  // outs() << endl;
  // outs() << "loVec: ";
  // for(auto ite = loVec.begin(); ite != loVec.end(); ite++)
  //     outs() << *ite << " ";
  // outs() << endl;

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

//normalize comparison expression through dividing both side
Expr multTrans(Expr t, Expr constVar)
{
  Expr lhs = t->left(), rhs = t->right();
  while(isOp<MULT>(lhs)) //until lhs is no longer *
  {
    Expr lOperand = lhs->left(), rOperand = lhs->right();
    bool yOnTheLeft = contains(lOperand, constVar);

    rhs = mk<DIV>(rhs, yOnTheLeft ? rOperand : lOperand);
    lhs = yOnTheLeft ? lOperand : rOperand;
    if (!contains(lhs, constVar))
      unreachable();
  }
  return (mk(t->op(), lhs, rhs));
}

/**
 * realQE - MBP procedure for LRA
 * @sSet: set of inequalities with eVar on lhs
 * @eVar: existentially quantified variable to be eliminated
 */
Expr realQE(ExprSet sSet, Expr eVar, ZSolver<EZ3>::Model &m)
{
  ExprVector sVec, upVec, loVec;

  for(auto t : sSet)
  {
    if(isOp<MULT>(t->left()))
      t = multTrans(t, eVar);
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

  return conjoin(outSet, eVar->getFactory());
}

/* INTEGER HELPER FUNCTION */
static Expr divTransHelper(Expr t, Expr constVar)
{
  // only for GT & LEQ Expr
  if(!isOpX<GT>(t) && !isOpX<LEQ>(t))
  {
    outs() << "Error, divTransInt(): " << *t << " is not GT nor LEQ." << endl;
    return t;
  }
  Expr lhs = t->left(), rhs = t->right();
  Expr one = mkTerm(mpz_class(1), t->getFactory());
  Expr y, coef;

  if(contains(lhs->left(), constVar))
    y = lhs->left(), coef = lhs->right();
  else
    assert(false);
  return mk(t->op(), y, mk<MINUS>(mk<MULT>(mk<PLUS>(rhs, one), coef), one));
}

// For single integer Expr normalization, only capable of handling LT & GEQ Exprs
Expr divMultTransInt(Expr t, Expr constVar)
{
  Expr lhs = t->left(), rhs = t->right();
  if (!isOp<MULT>(lhs) && !isOp<IDIV>(lhs))
    return t;

  if(lhs->arity() == 2)
  {
    int coef = 1;
    while(true)
    {
      // outs() << "t during transformation: " << *t << endl;
      if(lhs->arity() == 1)
        break;
      else if(isOpX<MULT>(lhs))
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
          outs() << "Error: " << *t
                 << " contains coefficient that's not a integer constant!"
                 << endl;
          exit(0); //critical Error
        }
      }
      else if(isOpX<IDIV>(lhs))
      {
        t = divTransHelper(t, constVar);
      }
      else
      {
        outs() << "Error, divMultTransInt(): Unexpected operation (not "
                  "idiv or "
                  "mult)."
               << endl;
        break;
      }
      lhs = t->left(), rhs = t->right();
    }
    // outs() << "divMultTransInt end: t " << mk(t->op(), lhs, rhs) << endl;
    if(coef > 1)
      return mk(
        t->op(), mk<MULT>(mkTerm(mpz_class(coef), t->getFactory()), lhs), rhs);
    else
      return mk(t->op(), lhs, rhs);
  }
  else
    return t;
}

static Expr vecElemInitInt(Expr t, Expr constVar)
{
  Expr lhs = t->left(), rhs = t->right();

  // get rid of LT and GEQ
  Expr constOne = mkTerm(mpz_class(1), t->getFactory());
  if(isOpX<LT>(t))
    t = mk<LEQ>(lhs, mk<MINUS>(rhs, constOne));
  else if(isOpX<GEQ>(t))
    t = mk<GT>(lhs, mk<MINUS>(rhs, constOne));

  t = divMultTransInt(t, constVar);

  return t;
}

// Helper function for coefTrans
Expr coefApply(Expr t, Expr constVar, int LCM)
{
  Expr lhs = t->left(), rhs = t->right();
  Expr newCoef = mkTerm(mpz_class(LCM), t->getFactory());
  if(isOp<MULT>(lhs))
  {
    Expr origCoef = (isOpX<MPZ>(lhs->left())) ? lhs->left() : lhs->right();
    Expr rhsCoef = mkTerm(
      mpz_class(LCM / boost::lexical_cast<int>(origCoef)), t->getFactory());
    rhs = mk<MULT>(rhsCoef, rhs);
  }
  else
    rhs = mk<MULT>(newCoef, rhs);
  lhs = mk<MULT>(newCoef, constVar);
  return (mk(t->op(), lhs, rhs));
}

int coefTrans(ExprVector &sVec, Expr constVar)
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
      *ite = coefApply(*ite, constVar, LCM);
  return LCM;
}

/**
 * intQE - MBP procedure for LIA
 * @sSet: set of inequalities with eVar on lhs
 * @eVar: existentially quantified variable to be eliminated
 */
Expr intQE(ExprSet sSet, Expr constVar, ZSolver<EZ3>::Model &m)
{
  Expr coefExpr = NULL;
  ExprSet outSet;
  ExprVector sVec, loVec, upVec;
  /* Transformation Stage */
  for(auto t : sSet)
  {
    Expr initEx = vecElemInitInt(t, constVar);
    sVec.push_back(initEx);
  }
  // Coefficient Transformation, and extract the coefficient.
  int coef = coefTrans(sVec, constVar);
  if(coef > 1)
    coefExpr = mkTerm(mpz_class(coef), constVar->getFactory());
  // Collecting upper & lower bound
  for(auto ite = sVec.begin(); ite != sVec.end(); ite++)
  {
    if(isOpX<GT>(*ite))
      loVec.push_back(*ite);
    else if(isOpX<LEQ>(*ite))
      upVec.push_back(*ite);
  }
  laMergeBounds(loVec, upVec, outSet, m, coefExpr);

  return conjoin(outSet, constVar->getFactory());
}

Expr ufo::mixQE(
  Expr s,
  Expr eVar,
  ZSolver<EZ3>::Model &m,
  SMTUtils &u,
  int debug)
{
  Expr output;
  ExprSet outSet, temp, sameTypeSet;
  if(eVar == NULL)
    return s; // nothing to eliminate
  Expr yType = bind::typeOf(eVar);

  // Boolean case.
  if(yType == mk<BOOL_TY>(s->efac()))
  {
    output = simplifyBool(mk<OR>(
      replaceAll(s, eVar, mk<TRUE>(s->efac())),
      replaceAll(s, eVar, mk<FALSE>(s->efac()))));
    return output;
  }
  // gather conjuncts that's the same type with y into sameTypeSet.
  getConj(s, temp);
  for(auto t : temp)
  {
    if (t == NULL)
      continue;

    if(!contains(t, eVar)) {
      outSet.insert(t);
      continue;
    }

    if(isOpX<NEG>(t) && isOp<ComparissonOp>(t->left()))
      t = mkNeg(t->left());
    if(isOp<ComparissonOp>(t))
    {
      t = simplifyArithm(reBuildCmp(
        t,
        mk<PLUS>(t->arg(0), additiveInverse(t->arg(1))),
        mkMPZ(0, s->efac())));
      t = ineqSimplifier(eVar, t);
    }
    else
      unreachable();
    int intVSreal = intOrReal(t);

    if(yType == mk<REAL_TY>(s->efac()) && (intVSreal == REALTYPE))
      sameTypeSet.insert(t);
    else if(yType == mk<INT_TY>(s->efac()) && (intVSreal == INTTYPE))
      sameTypeSet.insert(t);
    else if(intVSreal != NOTYPE)
      notImplemented();
  }

  if(sameTypeSet.empty()) // nothing to eliminate
    return conjoin(outSet, s->efac());

  outSet.insert(
    yType == mk<REAL_TY>(s->efac()) ? realQE(sameTypeSet, eVar, m)
                                    : intQE(sameTypeSet, eVar, m));
  output = conjoin(outSet, s->getFactory());
  return output;
}

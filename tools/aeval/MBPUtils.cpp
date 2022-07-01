#include "ae/MBPUtils.hpp"

#include "ae/AeValSolver.hpp"

using namespace ufo;

int intOrReal(Expr s)
{
    ExprVector sVec;
    int realCt = 0, intCt = 0;
    filter(s, bind::IsNumber(), back_inserter(sVec));
    filter(s, bind::IsConst(), back_inserter(sVec));
    for(auto ite : sVec)
    {
        if(isOpX<MPQ>(ite))
            outs() << "real? " << *ite << endl;
        if(bind::isIntConst(ite) || isOpX<MPZ>(ite))
            ++intCt;
        else if(bind::isRealConst(ite) || isOpX<MPQ>(ite))
            ++realCt;
        else
            outs() << "Error identifying: " << *ite << " in intOrReal()."
                   << endl;
    }
    if(realCt == 0 && intCt > 0)
        return 1;
    else if(realCt > 0 && intCt == 0)
        return -1;
    else if(realCt == 0 && intCt == 0)
        return 2;
    outs() << "For s: " << s << "\n\tCurrent realCt = " << realCt
           << "\n\tCurrent intCt = " << intCt << endl;
    return 0; //mixture of int and real.
}

// create forall & exists formulas
Expr ufo::createQuantifiedFormulaRestr(Expr def, Expr a, bool forall)
{ // want to have quantifiers in def
    ExprVector args;
    args.push_back(a->last()); // push variable y into vars.
    args.push_back(def);
    if(forall)
        return mknary<FORALL>(args);
    else
        return mknary<EXISTS>(args);
}

// overloaded create quantifiers that takes in ExprSet of vars.
Expr ufo::createQuantifiedFormulaRestr (Expr def, ExprSet& vars, bool forall)
{
  if (vars.empty()) return def;
  ExprVector args;
  for (auto & a : vars) args.push_back(a->last());
  args.push_back(def);
  if (forall) return mknary<FORALL>(args);
  else return mknary<EXISTS>(args);
}

// reverse the current comparison expression.
Expr revExpr(Expr s)
{
    Expr lhs = s->left(), rhs = s->right();
    if(isOpX<LT>(s))
        return mk<GT>(rhs, lhs);
    else if(isOpX<LEQ>(s))
        return mk<GEQ>(rhs, lhs);
    else if(isOpX<GT>(s))
        return mk<LT>(rhs, lhs);
    else if(isOpX<GEQ>(s))
        return mk<LEQ>(rhs, lhs);
    outs() << "Error in revExpr(): current comparison for expression ";
    outs() << *s << " is not supported." << endl;
    return NULL;
}

bool negCoefNumCheck(Expr lhs)
{
    if(isOpX<MULT>(lhs))
    {
        if(
          isOpX<MPZ>(lhs->left()) &&
          (boost::lexical_cast<int>(lhs->left()) < 0))
            return true;
        if(
          isOpX<MPZ>(lhs->right()) &&
          (boost::lexical_cast<int>(lhs->right()) < 0))
            return true;
    }
    return false;
}

//converting the negative coefficient into a positive coefficient that's being added an UN_MINUS.
Expr convertNegCoefNum(Expr t)
{
    if(!negCoefNumCheck(t->left()))
        return t; // if t doesn't contain negative coefficient, then do nothing.
    Expr coef = NULL, remain = NULL, lhs = t->left(), rhs = t->right();
    if(isOpX<MPZ>(lhs->left()))
        coef = lhs->left(), remain = lhs->right();
    else if(isOpX<MPZ>(lhs->right()))
        coef = lhs->right(), remain = lhs->left();
    if(coef != NULL)
    {
        coef = mk<UN_MINUS>(mkTerm(
          mpz_class(boost::lexical_cast<int>(coef) * -1), t->getFactory()));
        t = mk(t->op(), mk<MULT>(coef, remain), rhs);
    }
    else
        outs()
          << "Error, convertNegCoefNum: Unable to locate lhs coefficient.\n";
    return t;
}

// Move all neg coef to rhs so lhs doesn't have any negative coefficient
Expr negativeCoefCheck(Expr t)
{
    Expr lhs = t->left(), rhs = t->right();
    if(isOpX<UN_MINUS>(lhs->left()))
    {
        Expr coef = lhs->left()->left();
        lhs = mk(lhs->op(), coef, lhs->right());
    }
    else if(isOpX<UN_MINUS>(lhs->right()))
    {
        Expr coef = lhs->right()->left();
        lhs = mk(lhs->op(), lhs->left(), coef);
    }
    else
    {
        return t;
    }
    rhs = mk<MULT>(mk<UN_MINUS>(mkTerm(mpz_class(1), t->getFactory())), rhs);
    if(isOpX<LT>(t))
        return mk<GT>(lhs, rhs);
    else if(isOpX<LEQ>(t))
        return mk<GEQ>(lhs, rhs);
    else if(isOpX<GT>(t))
        return mk<LT>(lhs, rhs);
    else if(isOpX<GEQ>(t))
        return mk<LEQ>(lhs, rhs);
    outs()
      << "Error in negativeCoefCheck(): current comparison for expression ";
    outs() << *t << " is not supported." << endl;
    return NULL;
}

// Most basic initializer, also work as helper for vecElemInitInt & vecElemInitReal
Expr singleExprNormPrep(Expr t, Expr constVar, bool isInt = false)
{
    if(isOp<ComparissonOp>(t))
    {
        //ensure y is on lhs.
        if(contains(t->right(), constVar))
            t = revExpr(t);
        if(t == NULL)
            return NULL;
        //ensure lhs is not negative
        if(t->left()->arity() == 2)
        {
            if(isInt)
                t = convertNegCoefNum(t);
            t = negativeCoefCheck(t);
        }
        // constant change to lhs & rhs may occur, thus placing initialization in the middle.
        Expr lhs = t->left(), rhs = t->right();
        if(isInt)
        {
            //applying (3) to integer Expr, getting rid of LT and GEQ
            Expr constOne = mkTerm(mpz_class(1), t->getFactory());
            if(isOpX<LT>(t))
                t = mk<LEQ>(lhs, mk<MINUS>(rhs, constOne));
            else if(isOpX<GEQ>(t))
                t = mk<GT>(lhs, mk<MINUS>(rhs, constOne));
        }
        return t;
    }
    else
    {
        outs() << "Error, (singleExprNormPrep) The input Expr " << *t
               << " is not comparison!" << endl;
        return NULL;
    }
}

//normalize comparison expression through dividing both side
Expr multTrans(Expr t, Expr constVar)
{
    if(isOp<ComparissonOp>(t))
    {
        Expr lhs = t->left(), rhs = t->right();
        while(isOp<MULT>(lhs)) //until lhs is no longer *
        {
            bool divLeft;
            Expr lOperand = lhs->left(), rOperand = lhs->right();
            if(contains(lOperand, constVar))
                divLeft = false;
            else if(contains(rOperand, constVar))
                divLeft = true;
            else
                outs() << "Cannot find variable y in " << *lhs
                       << endl; //debug check
            rhs = mk<DIV>(rhs, divLeft ? lOperand : rOperand);
            lhs = divLeft ? rOperand : lOperand;
        }
        return (mk(t->op(), lhs, rhs));
    }
    else
    {
        outs() << "(multTrans) input Expr is not comparison!" << endl;
        return NULL;
    }
}

Expr vecElemInitReal(Expr t, Expr constVar)
{
    if(isOp<ComparissonOp>(t))
    {
        //EQ or NEQ expression are not currently supported.
        if(isOpX<EQ>(t) || isOpX<NEQ>(t))
            return NULL;
        t = singleExprNormPrep(t, constVar);
        if(t == NULL)
            return t;
        //MULTIPLICATION TRANSFORMATION
        if(isOp<MULT>(t->left()))
            t = multTrans(t, constVar);
        return t;
    }
    else
    {
        outs() << "(vecElemInitReal)The input Expr " << *t
               << " is not comparison!" << endl;
        return NULL;
    }
}

Expr realQE(ExprSet sSet, Expr constVar)
{
    ExprSet outSet, upVec, loVec;
    ExprVector sVec;
    Expr factoryGetter = *(sSet.begin());
    // Initializing Expression Vector, ensure y is not on rhs, ensure lhs doesn't have multiplication.
    for(auto t : sSet)
    {
        Expr initEx = vecElemInitReal(t, constVar);
        if(initEx != NULL)
            sVec.push_back(initEx);
        else
            outSet.insert(t);
    }
    // Collecting upper & lower bound
    for(auto ite = sVec.begin(); ite != sVec.end(); ite++)
    {
        if(isOpX<GT>(*ite) || isOpX<GEQ>(*ite))
            loVec.insert(*ite);
        else if(isOpX<LT>(*ite) || isOpX<LEQ>(*ite))
            upVec.insert(*ite);
    }
    sVec.clear();
    // Merging upper & lower bound.
    while(!loVec.empty())
    {
        Expr loBound = (*loVec.begin())->right();
        bool upGEQ = isOpX<GEQ>(*loVec.begin()) ? true : false;
        for(auto loIte = upVec.begin(); loIte != upVec.end(); ++loIte)
        {
            Expr upBound = (*loIte)->right();
            if(upGEQ && isOpX<LEQ>(*loIte))
                sVec.push_back(mk<LEQ>(loBound, upBound));
            else
                sVec.push_back(mk<LT>(loBound, upBound));
        }
        loVec.erase(loVec.begin());
    }
    for(auto t : sVec)
        outSet.insert(t);
    return conjoin(outSet, factoryGetter->getFactory());
}

/* INTEGER HELPER FUNCTION */
static Expr divTransHelper(Expr t, Expr constVar)
{ // only for GT & LEQ Expr
    if(isOpX<GT>(t) || isOpX<LEQ>(t))
    {
        Expr lhs = t->left(), rhs = t->right(), y, coef,
             one = mkTerm(mpz_class(1), t->getFactory());
        if(contains(lhs->left(), constVar))
            y = lhs->left(), coef = lhs->right();
        else
            y = lhs->right(), coef = lhs->left();
        return mk(
          t->op(), y, mk<MINUS>(mk<MULT>(mk<PLUS>(rhs, one), coef), one));
    }
    else
    {
        outs() << "Error, divTransInt(): " << *t << " is not GT nor LEQ."
               << endl;
        return t;
    }
}

// For single integer Expr normalization, only capable of handling LT & GEQ Exprs
Expr divMultTransInt(Expr t, Expr constVar)
{
    // outs() << "divMultTransInt begin: t " << t << endl;
    Expr lhs = t->left(), rhs = t->right();
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
                    outs()
                      << "Error: " << *t
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
              t->op(),
              mk<MULT>(mkTerm(mpz_class(coef), t->getFactory()), lhs),
              rhs);
        else
            return mk(t->op(), lhs, rhs);
    }
    else
        return t;
}

static Expr vecElemInitInt(Expr t, Expr constVar)
{
    // outs() << "VecElemInitInt beginning t: " << t << endl; //outTest
    if(isOp<ComparissonOp>(t))
    {
        //EQ or NEQ expression are not currently supported.
        if(isOpX<EQ>(t) || isOpX<NEQ>(t))
            return NULL;
        //ensure y is on lhs, lhs not negative, & get rid of LT and GEQ
        t = singleExprNormPrep(t, constVar, true);
        if(t == NULL)
            return t;
        // Single conjunct Mult & Div transformation.
        if(isOp<MULT>(t->left()) || isOp<IDIV>(t->left()))
            t = divMultTransInt(t, constVar);
        // outs() << "VecElemInitInt after t: " << *t << endl << endl; //outTest
        return t;
    }
    else
    {
        outs() << "(vecElemInitInt)The input Expr " << *t
               << " is not comparison!" << endl;
        return NULL;
    }
}

// helper to find least common multiple.
int findLCM(int a, int b)
{ // lcm(a,b) = a*b/gcd(a,b)
    int prod = a * b;
    while(a != b)
    {
        if(a > b)
            a = a - b;
        else
            b = b - a;
    }
    return prod / a;
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

ExprVector coefTrans(ExprVector sVec, Expr constVar)
{
    ExprVector outVec;
    int LCM = 1;
    vector<int> intVec;
    // Gather LCM
    for(auto ite = sVec.begin(); ite != sVec.end(); ite++)
    {
        // outs() << "\tite: " << *ite << endl;
        Expr lhs = (*ite)->left();
        if(isOp<MULT>(lhs))
        {
            if(isOpX<MPZ>(lhs->left()))
                intVec.push_back(boost::lexical_cast<int>(*lhs->left()));
            else if(isOpX<MPZ>(lhs->right()))
                intVec.push_back(boost::lexical_cast<int>(*lhs->right()));
            else
                outs() << "Coef not found in " << *ite << endl;
        }
    }
    for(auto i : intVec)
        LCM = findLCM(LCM, i);
    // Making all Coefs for y into LCM
    if(LCM > 1)
        for(auto t : sVec)
            outVec.push_back(coefApply(t, constVar, LCM));
    else
        for(auto t : sVec)
            outVec.push_back(t);
    // Append the coefficient at the end
    outVec.push_back(mkTerm(mpz_class(LCM), (*sVec.begin())->getFactory()));
    return outVec;
}

Expr intQE(ExprSet sSet, Expr constVar)
{
    ExprSet outSet, upVec, loVec;
    ExprVector sVec;
    Expr factoryGetter = *(sSet.begin());
    /* Transformation Stage */
    for(auto t : sSet)
    {
        Expr initEx = vecElemInitInt(t, constVar);
        if(initEx != NULL)
            sVec.push_back(initEx);
        else
            outSet.insert(t);
    }
    // Coefficient Transformation, and extract the coefficient.
    sVec = coefTrans(sVec, constVar);
    Expr coef = *(sVec.end() - 1);
    sVec.pop_back();
    // Collecting upper & lower bound
    for(auto ite = sVec.begin(); ite != sVec.end(); ite++)
    {
        if(isOpX<GT>(*ite))
            loVec.insert(*ite);
        else if(isOpX<LEQ>(*ite))
            upVec.insert(*ite);
    }
    sVec.clear();
    // Merging upper & lower bound.
    bool divFlag = boost::lexical_cast<int>(coef) > 1 ? true : false;
    while(!loVec.empty())
    {
        Expr loBound = (*loVec.begin())->right();
        for(auto loIte = upVec.begin(); loIte != upVec.end(); ++loIte)
        {
            Expr upBound = (*loIte)->right();
            sVec.push_back(mk<LT>(loBound, upBound));
            if(divFlag)
                sVec.push_back(
                  mk<LT>(mk<IDIV>(loBound, coef), mk<IDIV>(upBound, coef)));
        }
        loVec.erase(loVec.begin());
    }
    for(auto t : sVec)
        outSet.insert(t);
    return conjoin(outSet, factoryGetter->getFactory());
}

Expr ufo::mixQE(
  Expr s,
  Expr constVar,
  ExprMap &substsMap,
  ZSolver<EZ3>::Model &m,
  SMTUtils &u,
  int debug)
{
    Expr orig = createQuantifiedFormulaRestr(s, constVar), output;
    ExprSet outSet, temp, sameTypeSet;
    if(constVar == NULL)
        return s; // taking care of the y does not exist situation.
    Expr yType = bind::typeOf(constVar); // identify and store the type of y.
    // outs() << "constVar: " << *constVar << ", type: " << *yType << endl; //outTest
    // Support for boolean case.
    if(yType == mk<BOOL_TY>(s->efac()))
    {
        if(m.eval(constVar) != constVar)
            substsMap[constVar] = mk<EQ>(constVar, m.eval(constVar));
        output = simplifyBool(mk<OR>(
          replaceAll(s, constVar, mk<TRUE>(s->efac())),
          replaceAll(s, constVar, mk<FALSE>(s->efac()))));
        if(debug)
        {
            // outs() << "Before mixQE: " << orig << "\nAfter mixQE: " << output
                //    << endl; //outTest
            // outs() << "mixQE() Equivalence Check: " << u1.isEquiv(orig, output) << endl << endl; //outTest
            boost::tribool equiv = u.isEquiv(orig, output);
            if(boost::indeterminate(equiv))
                outs() << "Solver returned undefined" << endl;
            assert(equiv);
            assert(not (contains(output, constVar)));
        }
        return output;
    }
    // gather conjuncts that's the same type with y into sameTypeSet.
    getConj(s, temp);
    for(auto t : temp)
    {
        if(contains(t, constVar))
        {
            if(isOpX<NEG>(t) && isOp<ComparissonOp>(t->left()))
                t = mkNeg(t->left());
            if(isOp<ComparissonOp>(t))
            {
                t = simplifyArithm(reBuildCmp(
                  t,
                  mk<PLUS>(t->arg(0), additiveInverse(t->arg(1))),
                  mkMPZ(0, s->efac())));
                t = ineqSimplifier(constVar, t);
            }
            else
            {
                assert(0);
            }
            int intVSreal = intOrReal(t);
            // outs() << bind::typeOf(t->right()) << "\nyType: " << yType << "\nintVSreal: " << intVSreal << endl; //outTest
            if(yType == mk<REAL_TY>(s->efac()) && (intVSreal == -1))
                sameTypeSet.insert(t);
            else if(yType == mk<INT_TY>(s->efac()) && (intVSreal == 1))
                sameTypeSet.insert(t);
            else if(intVSreal != 2)
            { // if intVSreal == 2, thus t == true, so do nothing in that case.
                outs() << "Nothing eliminated\nyType: " << yType
                       << "\nintVSreal: " << intVSreal << endl; //outTest
                outs() << "contains var? " << contains(s, constVar)
                       << endl; //outTest
                outs() << "s: " << s << endl;
                return s;
            } //no change can be made, return original expr.
        }
        else
            outSet.insert(t);
    }
    // outs() << "sameTypeSet: " << conjoin(sameTypeSet, s->getFactory()) << endl; // outTest
    if(sameTypeSet.empty())
        return conjoin(outSet, s->efac());
    // Append map to substsMap
    substsMap[constVar] = conjoin(sameTypeSet, s->getFactory());
    outSet.insert(
      yType == mk<REAL_TY>(s->efac()) ? realQE(sameTypeSet, constVar)
                                      : intQE(sameTypeSet, constVar));
    output = conjoin(outSet, s->getFactory()); //prepare for Sanity Check

    // SANITY CHECK
    if(debug)
    {
        // outs() << "Before mixQE: " << orig << "\nAfter mixQE: " << output
        //        << endl; //outTest
        // u1.print(output);
        // outs() << "\n";
        boost::tribool equiv = u.isEquiv(orig, output);
        if(boost::indeterminate(equiv))
            outs() << "Solver returned undefined" << endl;
        assert(equiv);
        assert(not (contains(output, constVar)));
    }
    return output;
}

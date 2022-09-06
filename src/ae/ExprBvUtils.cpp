#include "common.h"
#include "ae/ExprSimpl.hpp"
#include "ae/ExprBvUtils.hpp"

using namespace ufo;
using namespace boost::multiprecision;


typedef std::set<unsigned> uintSet;

void ufo::getSignedCmps (Expr a, ExprVector &scmps)
{
    if (isOp<BvSCmp>(a)){
        scmps.push_back(a);
    } else {
        for (unsigned i = 0; i < a->arity(); i++)
            getSignedCmps(a->arg(i), scmps);
    }
}

static void mineBvSizes(Expr exp, uintSet& sizes) 
{
    if (bv::is_bvnum(exp) || bv::is_bvconst(exp)) {
        sizes.insert(bv::width(exp->right()));
    } else if (isOp<BvArithOp>(exp) || isOp<BvOp>(exp)) {
        for (int i = 0; i < exp->arity(); i++)
            mineBvSizes(exp->arg(i), sizes);
    } else if (bv::isBvCmp(exp)) {
        mineBvSizes(exp->left(), sizes);
        mineBvSizes(exp->right(), sizes);
    } else if (isOp<BoolOp>(exp)) {
        for (int i = 0; i < exp->arity(); i++)
            mineBvSizes(exp->arg(i), sizes);
    } else {
        notImplemented();
    }
}

unsigned ufo::getBvSize(Expr exp) 
{
    uintSet sizes;
    mineBvSizes(exp, sizes);
    if (sizes.size() > 1) {
        errs() << "Invalid expression bitvectors of different sizes\n";
        criticalError();
    }
    unsigned bvSize = 0;
    for (unsigned a : sizes)
        bvSize = a;
    return bvSize;
}

static inline Expr bvConstFromNumber(int val, unsigned size, ExprFactory& efac)
{
    return bv::bvConst(mkTerm (mpz_class(val), efac), size);
}

Expr ufo::reBuildBvNegCmp(Expr fla, Expr lhs, Expr rhs)
{
    // signed cmps must be eliminated beforehand
    if (isOpX<BULE>(fla))
        return mk<BUGT>(lhs, rhs);
    else if (isOpX<BUGE>(fla))
        return mk<BULT>(lhs, rhs);
    else if (isOpX<BULT>(fla))
        return mk<BUGE>(lhs, rhs);
    assert(isOpX<BUGT>(fla));
    return mk<BULE>(lhs, rhs);
}

template <typename T> Expr rewriteSignedHelper(Expr exp)
{
    unsigned size = getBvSize(exp);
    ExprFactory& efac = exp->getFactory();
    Expr lhs = exp->left(), rhs = exp->right();

    int val = 2^(size - 1);
    Expr constBv = bvConstFromNumber(val, size, efac);
    ExprSet disjs, lconjs, rconjs;
    lconjs.insert(mk<BULT>(lhs, constBv));
    lconjs.insert(mk<BULT>(rhs, constBv));
    disjs.insert(conjoin(lconjs, efac));

    rconjs.insert(mk<BULE>(constBv, lhs));
    rconjs.insert(mk<BULE>(constBv, rhs));
    disjs.insert(conjoin(rconjs, efac));
    
    Expr cond = disjoin(disjs, efac);
    Expr elseBranch = mk<AND>(
                        mk<T>(constBv, lhs),
                        mk<T>(rhs, constBv));
    return mk<ITE>(cond, mk<T>(lhs, rhs), elseBranch);
}

Expr ufo::rewriteSignedCmp(Expr exp)
{
    if (isOpX<BSLE>(exp))
        return rewriteSignedHelper<BULE>(exp);
    else if (isOpX<BSGE>(exp))
        return rewriteSignedHelper<BULE>(exp);
    else if (isOpX<BSLT>(exp))
        return rewriteSignedHelper<BULT>(exp);
    else {
        assert(isOpX<BSGT>(exp));
        return rewriteSignedHelper<BUGT>(exp);
    }
}

bool ufo::isBvArith(Expr exp)
{
    if (bv::is_bvnum(exp) || bv::is_bvconst(exp)) {
        return true;
    } else if (isOp<BvUCmp>(exp) || isOp<BvArithOp>(exp)) {
        bool res = true;    
        for (int i = 0; i < exp->arity(); i++)
            res &= isBvArith(exp->arg(i));
        return res;
    } else {
        return false;
    }
}

Expr rewriteDivisible(Expr exp)
{
    unsigned size = getBvSize(exp);
    ExprFactory& efac = exp->getFactory();
    Expr lhs = exp->left(), rhs = exp->right();
    Expr bvZero = bvConstFromNumber(0, size, efac);
    Expr bvOne = bvConstFromNumber(1, size, efac);

    ExprSet disjs;
    disjs.insert(mk<EQ>(lhs, bvZero));

    Expr l = mk<BUDIV>(mk<BSUB>(lhs, bvOne), rhs);
    Expr r = mk<BUDIV>(lhs, rhs);
    disjs.insert(mk<BULT>(l, r));
    return disjoin(disjs, efac);
}

Expr rewriteRem(Expr exp)
{
    Expr lhs = exp->left(), rhs = exp->right();
    Expr r = mk<BMUL>(mk<BUDIV>(lhs, rhs), rhs);
    return mk<BSUB>(lhs, r);
}

Expr ufo::bvReBuildCmp(Expr exp, Expr lhs, Expr rhs)
{
    if (isOpX<BULE>(exp))
        return mk<BUGE>(rhs, lhs);
    else if (isOpX<BUGE>(exp))
        return mk<BULE>(rhs, lhs);
    else if (isOpX<BULT>(exp))
        return mk<BULE>(rhs, lhs);
    assert(isOpX<BUGT>(exp));
    return mk<BULT>(rhs, lhs);
}

bool ufo::isBmulVar(Expr e, Expr var)
{
    if (!isOpX<BMUL>(e)) return false;
    else if (bv::is_bvnum(e->right()) && var == e->left()) return true;
    else if (bv::is_bvnum(e->left()) && var == e->right()) return true;
    return false;
}

Expr ufo::bvAdditiveInverse(Expr e)
{
    if (isOpX<BADD>(e))
    {
      ExprVector terms;
      for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
      {
        getBaddTerm(bvAdditiveInverse(*it), terms);
      }
      return mkbadd(terms);
    }
    else if (isOpX<BSUB>(e))
    {
      ExprVector terms;
      getBaddTerm(bvAdditiveInverse(*e->args_begin ()), terms);
      auto it = e->args_begin () + 1;
      for (auto end = e->args_end (); it != end; ++it)
      {
        getBaddTerm(*it, terms);
      }
      return mkbadd(terms);
    }
    else if (isOpX<BNEG>(e))
    {
      return e->left();
    }
    else if (isOpX<ITE>(e))
    {
      return mk<ITE>(e->left(), bvAdditiveInverse(e->right()), bvAdditiveInverse(e->last()));
    }

    return mk<BNEG>(e);
}

void ufo::getBaddTerm (Expr a, ExprVector &terms)
{   
    if (isOpX<BADD>(a))
    {
        for (auto it = a->args_begin (), end = a->args_end (); it != end; ++it)
        {
            getBaddTerm(*it, terms);
        }
    }
    else if (isOpX<BSUB>(a))
    {
        auto it = a->args_begin ();
        auto end = a->args_end ();
        getBaddTerm(*it, terms);
        ++it;
        for (; it != end; ++it)
        {
            getBaddTerm(bvAdditiveInverse(*it), terms);
        }
    }
    else if (isOpX<BNEG>(a))
    {
        ExprVector tmp;
        getBaddTerm(a->left(), tmp);
        for (auto & t : tmp)
        {
            bool toadd = true;
            for (auto it = terms.begin(); it != terms.end(); )
            {
                if (*it == t)
                {
                    terms.erase(it);
                    toadd = false;
                    break;
                }
                else ++it;
            }
            if (toadd) terms.push_back(bvAdditiveInverse(t));
        }
    }
    else if (isOpX<BMUL>(a))
    {
        Expr tmp = rewriteBmulBadd(a);
        if (tmp == a) terms.push_back(a);
        else getBaddTerm(tmp, terms);
    }
    // else if (bv::is_bvnum(a) && lexical_cast<string>(a->left()) == "0") 
    // {
    //     // do nothing
    // }
    else
    {
        bool found = false;
        for (auto it = terms.begin(); it != terms.end(); )
        {
            if (bvAdditiveInverse(*it) == a)
            {
                terms.erase(it);
                found = true;
                break;
            }
            else ++it;
        }
        if (!found) terms.push_back(a);
    }
}

void ufo::getBvMultVars(Expr e, Expr var, ExprVector& outs)
{
    ExprVector adds;
    getBaddTerm(e, adds);
    for (auto a : adds)
    {
        if (contains(a, var))
            outs.push_back(a);
    }
}
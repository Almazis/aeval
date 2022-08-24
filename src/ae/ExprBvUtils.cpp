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

static void mineBvSizes(Expr exp, uintSet& sizes) {
    if (bv::is_bvnum(exp) || bv::is_bvvar(exp)) {
        sizes.insert(bv::width(exp->right()));
    } else if (isOp<BvArithOp>(exp) || isOp<BvOp>(exp)){
        for (int i = 0; i < exp->arity(); i++)
            mineBvSizes(exp->arg(i), sizes);
    } else if (bv::isBvCmp(exp)) {
        mineBvSizes(exp->left(), sizes);
        mineBvSizes(exp->right(), sizes);
    } else if (isOp<BoolOp>(exp)) {
        for (int i = 0; i < exp->arity(); i++)
            mineBvSizes(exp->arg(i), sizes);
    } else {
        // outs() << exp << endl;
        // outs() << exp->right() << endl;
        // outs() << exp->left() << endl;
        notImplemented();
    }
}

unsigned ufo::getBvSize(Expr exp) {
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
    if (isOpX<BULE>(fla))
        return mk<BUGT>(lhs, rhs);
    else if (isOpX<BUGE>(fla))
        return mk<BULT>(lhs, rhs);
    else if (isOpX<BULT>(fla))
        return mk<BUGE>(lhs, rhs);
    else if (isOpX<BUGT>(fla))
        return mk<BULE>(lhs, rhs);
    
    else if (isOpX<BSLE>(fla))
        return mk<BSGT>(lhs, rhs);
    else if (isOpX<BSGE>(fla))
        return mk<BSLT>(lhs, rhs);
    else if (isOpX<BSLT>(fla))
        return mk<BSGE>(lhs, rhs);
    assert(isOpX<BSGT>(fla));
    return mk<BSLE>(lhs, rhs);
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

Expr rewriteDivisible(Expr exp) {
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

Expr rewriteRem(Expr exp) {
    Expr lhs = exp->left(), rhs = exp->right();
    Expr r = mk<BMUL>(mk<BUDIV>(lhs, rhs), rhs);
    return mk<BSUB>(lhs, r);
}

// normalization rules

// t(x) + y <= z ---> t(x) <= z-y && y <= z
Expr add1(Expr xPart, Expr yPart, Expr zPart) 
{
    Expr l = mk<BULE>(xPart, mk<BSUB>(zPart, yPart));
    Expr r = mk<BULE>(yPart, zPart);
    return mk<AND>(l, r);
}

// t(x) + y <= z ---> t(x) <= z-y && -y <= t(x)
Expr add2(Expr xPart, Expr yPart, Expr zPart) 
{
    ExprFactory& efac = xPart->getFactory();
    unsigned size = getBvSize(yPart);
    Expr bvZero = bvConstFromNumber(0, size, efac);
    Expr l = mk<BULE>(xPart, mk<BSUB>(zPart, yPart));
    Expr r = mk<BULE>(mk<BSUB>(bvZero, yPart), zPart);
    outs() << "\n";
    return mk<AND>(l, r);
}

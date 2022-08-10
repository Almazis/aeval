#include "ae/ExprSimpl.hpp"
#include "common.h"

using namespace ufo;
using namespace boost::multiprecision;


typedef std::set<unsigned> uintSet;

static void mineBvSizes(Expr exp, uintSet& sizes) {
    if (bv::is_bvnum(exp)) {
        sizes.insert(bv::width(exp));
    } else if (isOp<BvArithOp>(exp)){
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

unsigned getSize(Expr exp) {
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

Expr rewriteSCmp(Expr exp) {
    unsigned size = getSize(exp);
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
                        mk<BULE>(constBv, lhs),
                        mk<BULE>(rhs, constBv));
    return mk<ITE>(cond, mk<BULE>(lhs, rhs), elseBranch);
}

Expr rewriteDivisible(Expr exp) {
    unsigned size = getSize(exp);
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

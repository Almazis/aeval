#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include <catch2/catch.hpp>
#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"
#include "ufo/ExprBv.hh"
#include "ae/ExprBvUtils.hpp"
#include "ae/ExprSimpl.hpp"

using namespace ufo;
using namespace bv;

TEST_CASE("Mine size of bv const", "[Bv]") {
    ExprFactory efac;
    for(unsigned size = 1; size <= 64; size++) {
        Expr bvec = bv::bvnum(mpz_class(1), size, efac);
        REQUIRE(isBv(bvec));
        REQUIRE(getBvSize(bvec) == size);
    }
}

TEST_CASE("Mine size of bv arith", "[Bv]") {
    ExprFactory efac;
    for(unsigned size = 1; size <= 64; size++) {
        Expr bvec1 = bv::bvnum(mpz_class(1), size, efac);
        Expr bvec2 = bv::bvnum(mpz_class(1), size, efac);
        Expr bop = mk<BADD>(bvec1, bvec2);
        REQUIRE(isBv(bop));
        REQUIRE(getBvSize(bop) == size);
    }
}

TEST_CASE("Get badd terms", "[Bv]") {
    ExprFactory efac;
    ExprVector terms;
    unsigned size = 4;
    // for(unsigned size = 1; size <= 64; size++) {
    Expr bvec1 = bv::bvnum(mpz_class(1), size, efac);
    Expr bvec2 = bv::bvnum(mpz_class(2), size, efac);
    Expr e = mk<BADD>(bvec1, bvec2);
    Expr e1 = mk<BMUL>(bvec2, e);
    
    getBaddTerm(e1, terms);
    outs() << e1 << endl;
    for (auto t : terms)
        outs() << t << endl;
    // }    
}
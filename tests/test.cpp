#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include <catch2/catch.hpp>
#include "ae/MBPUtils.hpp"

using namespace ufo;

TEST_CASE( "Get constants types", "[MBPUtils]") {
    ExprFactory efac;
    Expr oneZ = mkTerm(mpz_class(1), efac);
    Expr oneQ = mkTerm(mpq_class(1), efac);
    Expr minusMix = mk<MINUS>(oneZ, oneQ);
    REQUIRE(intOrReal(oneZ) == INTTYPE);
    REQUIRE(intOrReal(oneQ) == REALTYPE);
    REQUIRE(intOrReal(minusMix) == MIXTYPE);
}

#ifndef SIMSYNT__HPP__
#define SIMSYNT__HPP__

#include "adt/ADTSolver.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class SimSynt
  {
    private:

    ExprFactory &efac;
    SMTUtils u;
    ExprVector &opsAdt;
    ExprVector &opsArr;

    public:

    SimSynt(ExprFactory& _efac, ExprVector& _ops1, ExprVector& _ops2, ExprVector& _c) :
      efac(_efac), u(_efac), opsAdt(_ops1), opsArr(_ops2), constructors(_c) {}

    ExprVector& constructors;
    Expr adtType;
    Expr baseCon;
    Expr indCon;
    ExprMap varVersions;
    ExprMap varVersionsInverse;
    Expr baseFormula;
    int stateProducingOp = -1;
    int stateConsumingOp = -1;

    void getVarVersions(Expr op)
    {
      ExprSet vars;
      filter(op, bind::IsConst (), inserter(vars, vars.begin()));
      for (auto & v : vars)
      {
        string str = lexical_cast<string>(v);
        if (str.back() == '1')
        {
          str.pop_back();
          for (auto & v1 : vars)
          {
            if (str == lexical_cast<string>(v1))
            {
              varVersionsInverse[v] = v1;
              varVersions[v1] = v;
              break;
            }
          }
        }
      }
    }

    bool isBaseConstructor(Expr c, Expr type)
    {
      return (c->last() == type && c->arity() == 2);
    }

    bool isIndConstructor(Expr c, Expr type)
    {
      if (c->last() != type) return false;
      for (int j = 0; j < c->arity() - 1; j++)
        if (c->last() == c->arg(j)) return true;

      return false;
    }

    void checkConstructor(int i)
    {
      ExprSet cnjs;
      getConj(opsAdt[i], cnjs);
      for (auto & op : cnjs)
      {
        for (auto & c : constructors)
        {
          Expr capp;
          if (isOpX<EQ>(op))
          {
            Expr lhs = op->left();
            Expr rhs = op->right();
            if (isOpX<FAPP>(rhs) && rhs->left() == c) capp = rhs;
            else if (isOpX<FAPP>(lhs) && lhs->left() == c) capp = lhs;
          }
          if (capp != NULL)
          {
            if (isBaseConstructor(c, bind::typeOf(capp)))
            {
              // first comes firts serve here (to be generalized)
              if (baseCon == NULL) baseCon = capp;
              if (baseFormula == NULL) baseFormula = opsArr[i];
              return;
            }
            else if (isIndConstructor(c, bind::typeOf(capp)))
            {
              // first comes first serve here (to be generalized)
              if (indCon == NULL) indCon = capp;
              bool found = false;
              for (auto & v : varVersionsInverse)
                found |= contains(capp, v.first);

              if (!found)
              {
                stateProducingOp = i; // TODO: check if several
              }
              else
              {
                stateConsumingOp = i;
              }
              return;
            }
          }
        }
      }
    }

    Expr createQuantifiedFormula(Expr def)
    {
      ExprSet vars;
      ExprVector args;
      filter(def, bind::IsConst (), inserter(vars, vars.begin()));
      for (auto & a : vars) if (a != baseCon) args.push_back(a->last());
      args.push_back(def);
      return mknary<FORALL>(args);
    }

    void proc()
    {
      assert(opsAdt.size() == opsArr.size());

      // preprocessing
      for (int i = 0; i < opsAdt.size(); i++)
      {
        getVarVersions(opsAdt[i]);
        getVarVersions(opsArr[i]);
        checkConstructor(i);
      }

      adtType = bind::typeOf(indCon);

      assert(adtType == bind::typeOf(indCon));
      assert(stateProducingOp >= 0);
//      assert(stateConsumingOp >= 0); // not used (yet)
      assert(baseFormula != NULL);
      assert(isOpX<EQ>(baseFormula));

      // get vars, types and arguments for rules of R
      ExprVector types;
      ExprVector vars;
      ExprVector argsBase;
      ExprVector argsInd;

      for (auto & p : varVersions)
      {
        Expr v = p.first;
        vars.push_back(v);
        types.push_back(bind::typeOf(v));

        if (bind::typeOf(v) == adtType)
        {
          argsBase.push_back(baseCon);
        }
        else
        {
          if (varVersions[v] == NULL)
          {
            outs () << "NO UNPRIMED VAR FOR " << *v <<"\n";
            return;
          }
          argsBase.push_back(v);
        }
        if (bind::typeOf(v) == adtType)
          argsInd.push_back(indCon);   // unprimed
        else
          argsInd.push_back(v);
      }

      types.push_back (mk<BOOL_TY> (efac));
      Expr rel = bind::fdecl (mkTerm<string> ("R", efac), types);
      Expr baseApp = bind::fapp (rel, argsBase);
      Expr baseDef = mk<EQ>(baseApp, baseFormula);

      // create a quantified formula representing the base rule of R
      Expr baseRule = createQuantifiedFormula(baseDef);
      u.serialize_formula(baseRule);

      // prepare for the inductive rule construction
      ExprSet counters;
      getCounters (opsArr[stateProducingOp], counters);
      assert(counters.size() == 1); // GF: to extend when needed
      Expr counter = *counters.begin();
      Expr accessTerm;

      // identify how elements in the arrays are accessed (i.e., the counter)
      ExprSet transitions;
      getConj(opsArr[stateProducingOp], transitions);
      for (auto tr : transitions)
      {
        if (contains (tr, counter) && !containsOp<ARRAY_TY>(tr))
        {
          tr = normalizeArithm(tr);
          tr = ineqSimplifier(counter, tr);
          assert(tr->left() == counter);
          accessTerm = replaceAll(tr->right(), varVersionsInverse);
          break;
        }
      }

      assert(accessTerm != NULL);

      // calculate the least fixedpoint over the counter variable
      // currently, a simple heuristic is used, but it can be extended
      ExprSet guesses;
      mutateHeuristic (baseFormula, guesses);
      Expr invariant;
      for (auto & g : guesses)
      {
        if (u.implies(baseFormula, g) &&
            u.implies (mk<AND>(g, opsArr[stateProducingOp]), replaceAll(g, varVersions)))
        {
          invariant = g;
          break;
        }
      }

      // TODO: further, this invariant can be used to generate an auxiliary lemma
      //       e.g., \forall xs, n, A . R (xs, n, A) => invariant (n)

      // get the "precondition" for the inductive rule of R:
      // it should follow the fixedpoint but inconsistent with
      // the precondition for the base rule of R (captured in baseFormula)
      assert (invariant != NULL);
      Expr remainingCnj = mk<AND>(invariant, mkNeg(baseFormula));

      // prepare for the nested call of R in the inductive rule of R
      Expr freshElem; // GF: to extend to ExprSet when needed
      Expr prevAdt;
      for (int j = 1; j < indCon->arity(); j++)
      {
        if (adtType == bind::typeOf(indCon->arg(j))) prevAdt = indCon->arg(j);
        else freshElem = indCon->arg(j);
      }
      int arrVarInd = -1;
      for (int j = 0; j < types.size(); j++) if (isOpX<ARRAY_TY>(types[j])) arrVarInd = j;

      // get arguments of the nested call of R
      ExprVector argsIndNested = argsInd;
      for (int j = 0; j < types.size(); j++)
      {
        if (isOpX<AD_TY>(types[j])) argsIndNested[j] = prevAdt;
        if (argsInd[j] == counter
              /*types[j] == bind::typeOf(counter)*/) argsIndNested[j] = accessTerm;
      }

      // prepare the inductive definition of R (i.e., the RHS of the inductive rule)
      ExprSet cnjs;
      cnjs.insert(bind::fapp (rel, argsIndNested));
      cnjs.insert(mk<EQ>(freshElem, mk<SELECT>(vars[arrVarInd], accessTerm)));
      cnjs.insert(remainingCnj);
      Expr inductiveDef = mk<EQ>(bind::fapp (rel, argsInd), conjoin(cnjs, efac));

      // create a quantified formula representing the inductive rule
      Expr indRule = createQuantifiedFormula(inductiveDef);
      u.serialize_formula(indRule);
    }
  };

  // non-recursive version (don't be confused with ExprSimpl.hpp::getConj(Expr a, ExprSet &conjs))
  static inline void getConj(Expr s, ExprVector& ops)
  {
    if (isOpX<AND>(s))
    {
      for (unsigned i = 0; i < s->arity(); i++)
      {
        ops.push_back(s->arg(i));
      }
    }
    else ops.push_back(s);
  }

  static inline void simSynt(ExprFactory& efac, EZ3& z3, Expr s1, Expr s2)
  {
    ExprVector constructors;
    for (auto & a : z3.getAdtConstructors()) constructors.push_back(a);
    ExprVector opsAdt;
    ExprVector opsArr;
    if (containsOp<AD_TY>(s1))
    {
      assert(containsOp<ARRAY_TY>(s2));
      getConj(s1, opsAdt);
      getConj(s2, opsArr);
    }
    else
    {
      assert(containsOp<ARRAY_TY>(s1));
      assert(containsOp<AD_TY>(s2));
      getConj(s2, opsAdt);
      getConj(s1, opsArr);
    }
    SimSynt sim(efac, opsAdt, opsArr, constructors);
    sim.proc();
  }
}

#endif

#include "ae/AeValSolver.hpp"

#include "ae/MBPUtils.hpp"

using namespace ufo;

void AeValSolver::getMBPandSkolem(ZSolver<EZ3>::Model &m)
{
  Expr pr = t, tempPr = t;
  ExprMap substsMap;
  ExprMap modelMap;
  for(auto &exp : v)
  {
    ExprMap map;
    ExprSet lits;
    u.getTrueLiterals(pr, m, lits, false);
    tempPr = z3_qe_model_project_skolem(z3, m, exp, conjoin(lits, efac), map);
    pr = simplifyArithm(mixQE(conjoin(lits, efac), exp, substsMap, m));
    if(m.eval(exp) != exp)
      modelMap[exp] = mk<EQ>(exp, m.eval(exp));

    if(debug >= 2)
    {
      outs() << "\nmodel " << partitioning_size << ":\n";
      for(auto &exp : stVars)
      {
        if(exp != m.eval(exp))
        {
          outs() << "[" << *exp << "=" << *m.eval(exp) << "],";
        }
      }
      outs() << "\n";
      outs() << "model map: \n";
      for(auto &m : modelMap)
      {
        pprint(m.second, 2);
      }
      outs() << "projection:\n";
      pprint(pr, 2);
    }

    for(auto it = lits.begin(); it != lits.end();)
    {
      if(contains(*it, exp))
        ++it;
      else
        it = lits.erase(it);
    }
    substsMap[exp] = conjoin(lits, efac);
  }

  if(debug)
    assert(emptyIntersect(pr, v));

  someEvals.push_back(modelMap);
  skolMaps.push_back(substsMap);
  projections.push_back(pr);
  partitioning_size++;
}

/**
* Decide validity of \forall s => \exists v . t
*/
boost::tribool AeValSolver::solve()
{
  smt.reset();
  smt.assertExpr(s);

  if(!smt.solve())
  {
    if(debug)
      outs() << "The S-part is unsatisfiable;\nFormula is trivially valid\n";
    return false;
  }
  else
  {
    ZSolver<EZ3>::Model m = smt.getModel();

    for(auto &e : sVars)
      // keep a model in case the formula is invalid
      modelInvalid[e] = m.eval(e);
  }

  if(v.size() == 0)
  {
    smt.assertExpr(boolop::lneg(t));
    boost::tribool res = smt.solve();
    return res;
  }

  smt.push();
  smt.assertExpr(t);

  boost::tribool res = true;

  while(smt.solve())
  {
    outs().flush();

    ZSolver<EZ3>::Model m = smt.getModel();

    getMBPandSkolem(m);
    smt.pop();
    smt.assertExpr(boolop::lneg(projections.back()));
    if(!smt.solve())
    {
      res = false;
      break;
    }
    else
    {
      // keep a model in case the formula is invalid
      m = smt.getModel();
      for(auto &e : sVars)
        modelInvalid[e] = m.eval(e);
    }

    smt.push();
    smt.assertExpr(t);
  }
  return res;
}

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
        tempPr =
          z3_qe_model_project_skolem(z3, m, exp, conjoin(lits, efac), map);
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
            outs()
              << "The S-part is unsatisfiable;\nFormula is trivially valid\n";
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

/**
 * Simple wrapper
 */
void ufo::aeSolveAndSkolemize(
  Expr s,
  Expr t,
  bool skol,
  int debug,
  bool opt,
  bool compact,
  bool split)
{
    ExprSet fa_qvars, ex_qvars;
    ExprFactory &efac = s->getFactory();
    SMTUtils u(efac);
    if(t == NULL)
    {
        if(!(isOpX<FORALL>(s) && isOpX<EXISTS>(s->last())))
            exit(0);
        s = regularizeQF(s);
        t = s->last()->last();
        for(int i = 0; i < s->last()->arity() - 1; i++)
            ex_qvars.insert(bind::fapp(s->last()->arg(i)));
        for(int i = 0; i < s->arity() - 1; i++)
            fa_qvars.insert(bind::fapp(s->arg(i)));

        s = mk<TRUE>(efac);
    }
    else
    {
        filter(s, bind::IsConst(), inserter(fa_qvars, fa_qvars.begin()));
        filter(t, bind::IsConst(), inserter(ex_qvars, ex_qvars.begin()));
        minusSets(ex_qvars, fa_qvars);
    }

    s = convertIntsToReals<DIV>(s);
    t = convertIntsToReals<DIV>(t);

    if(debug >= 3)
    {
        outs() << "s part: " << s << "\n";
        outs() << "t part: " << t << "\n";
        outs() << "s vars: [ ";
        for(auto &v : fa_qvars)
            outs() << v << " ";
        outs() << "]\n";
        outs() << "t vars: [ ";
        for(auto &v : ex_qvars)
            outs() << v << " ";
        outs() << "]\n";
    }

    Expr t_orig = t;
    if(opt)
    {
        ExprSet cnjs;
        getConj(t, cnjs);
        constantPropagation(fa_qvars, cnjs, true);
        // t = simpEquivClasses(fa_qvars, cnjs, efac);
        t = conjoin(cnjs, efac);
        t = simpleQE(t, ex_qvars);
        t = simplifyBool(t);
        if(debug >= 5)
        {
            outs() << "t part simplified: " << t << "\n";
        }
    }

    AeValSolver ae(s, t, ex_qvars, debug, skol);

    if(ae.solve())
    {
        outs() << "Iter: " << ae.getPartitioningSize() << "; Result: invalid\n";
        ae.printModelNeg(outs());
        outs() << "\nvalid subset:\n";
        u.serialize_formula(
          simplifyBool(simplifyArithm(ae.getValidSubset(compact))));
    }
    else
    {
        outs() << "Iter: " << ae.getPartitioningSize() << "; Result: valid\n";
        if(skol)
        {
            Expr skol = ae.getSkolemFunction(compact);
            if(split)
            {
                ExprVector sepSkols;
                for(auto &evar : ex_qvars)
                    sepSkols.push_back(mk<EQ>(
                      evar,
                      simplifyBool(simplifyArithm(ae.getSeparateSkol(evar)))));
                u.serialize_formula(sepSkols);
                if(debug)
                    outs() << "Sanity check [split]: "
                           << (bool)(u.implies(
                                mk<AND>(s, conjoin(sepSkols, s->getFactory())),
                                t_orig))
                           << "\n";
            }
            else
            {
                outs() << "\nextracted skolem:\n";
                u.serialize_formula(simplifyBool(simplifyArithm(skol)));
                if(debug)
                    outs() << "Sanity check: "
                           << (bool)(u.implies(mk<AND>(s, skol), t_orig))
                           << "\n";
            }
        }
    }
}

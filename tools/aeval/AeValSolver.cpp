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
        u.getTrueLiterals(pr, m, lits, true);
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
    MBPSanityCheck(m, tempPr, pr);
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

void AeValSolver::lastSanityCheck()
{
    ExprVector args;
    for (auto temp : v) args.push_back(temp->last());
    args.push_back(mk<IMPL>(s, t));
    Expr sImpT =  mknary<EXISTS>(args);
    Expr disjProj = mk<IMPL>(s, disjoin(projections, efac));
    // outs() << "\nDisjunctions of projections: " << *disjProj << "\n";
    // outs() << "exists v. s => t: " << sImpT << endl; //outTest
    // u.print(disjProj);
    // outs () << "\n\n";
    // u.print(sImpT);
    // outs () << "\n\n";
    SMTUtils u1(t->getFactory());
    // outs() << "'exists v. s => t' isEquiv to 'disjunctions of projections': ";
    // outs () << bool(u1.implies(disjProj, sImpT));
    // outs () << bool(u1.implies(sImpT, disjProj)) << "\n\n\n\n";
    assert(u1.implies(disjProj, sImpT));
    assert(u1.implies(sImpT, disjProj));
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
    outs() << "t at beginning of aeSolveAndSkolemize" << t << endl;
    ExprSet t_quantified;
    if(t == NULL)
    {
        if(!(isOpX<FORALL>(s) && isOpX<EXISTS>(s->last())))
            exit(0);

        s = regularizeQF(s);
        t = s->last()->last();
        for(int i = 0; i < s->last()->arity() - 1; i++)
            t_quantified.insert(bind::fapp(s->last()->arg(i)));

        s = mk<TRUE>(s->getFactory());
    }
    else
    {
        ExprSet s_vars;
        ExprSet t_vars;

        filter(s, bind::IsConst(), inserter(s_vars, s_vars.begin()));
        filter(t, bind::IsConst(), inserter(t_vars, t_vars.begin()));

        t_quantified = t_vars;
        minusSets(t_quantified, s_vars);
    }

    s = convertIntsToReals<DIV>(s);
    t = convertIntsToReals<DIV>(t);

    SMTUtils u1(s->getFactory()); //for future t equivalence test.

    Expr t_orig = t;
    Expr t_orig_qua = createQuantifiedFormulaRestr(t_orig, t_quantified);

    t = simplifyBool(t);
    ExprSet hardVars, cnjs;
    filter(t, bind::IsConst(), inserter(hardVars, hardVars.begin()));
    Expr t_qua = createQuantifiedFormulaRestr(t, t_quantified);

    getConj(t, cnjs);
    minusSets(hardVars, t_quantified);
    // outs() << "hardVars after minusSets: " << conjoin(hardVars, t->getFactory()) << endl;

    ExprSet elimSkol; // eliminated skolems
    constantPropagation(hardVars, cnjs, elimSkol, true);

    t = simpleQE(conjoin(cnjs, t->getFactory()), t_quantified, elimSkol);
    t = simplifyBool(t);

    if(debug && false) // outTest
    {
        outs() << "S: " << *s << "\n";
        outs() << "T: \\exists ";
        for(auto &a : t_quantified)
            outs() << *a << ", ";
        outs() << *t << "\n";
    }

    SMTUtils u(s->getFactory());
    AeValSolver ae(s, t, t_quantified, debug, skol);

    if(ae.solve())
    {
        outs() << "Iter: " << ae.getPartitioningSize() << "; Result: invalid\n";
        ae.lastSanityCheck();
        ae.printModelNeg(outs());
        outs() << "\nvalid subset:\n";
        u.serialize_formula(
          simplifyBool(simplifyArithm(ae.getValidSubset(compact))));
    }
    else
    {
        outs() << "Iter: " << ae.getPartitioningSize() << "; Result: valid\n";
        ae.lastSanityCheck();
        if(skol)
        {
            Expr skol = ae.getSkolemFunction(compact);
            if(split)
            {
                outs() << "\telimSkol: " << conjoin(elimSkol, s->getFactory())
                       << endl;
                ExprVector sepSkols;
                for(auto &evar : t_quantified)
                    sepSkols.push_back(mk<EQ>(
                      evar,
                      simplifyBool(simplifyArithm(ae.getSeparateSkol(evar)))));
                for(auto t : elimSkol)
                    sepSkols.push_back(t);
                u.serialize_formula(sepSkols);
                if(debug)
                {
                    for(auto t : elimSkol)
                        sepSkols.push_back(t);
                    // outs() << "Sanity check [split]: "
                    //        << u.implies(
                    //             mk<AND>(s, conjoin(sepSkols, s->getFactory())),
                    //             t_orig)
                    //        << "\n";
                }

                // u.outSanCheck("extractedSanChecks/multEx10.smt2");
            }
            else
            {
                outs() << "\nextracted skolem:\n";
                u.serialize_formula(simplifyBool(simplifyArithm(skol)));
                // if(debug)
                    // outs() << "Sanity check: "
                        //    << u.implies(mk<AND>(s, skol), t_orig) << "\n";
            }
        }
    }
}

void AeValSolver::MBPSanityCheck(ZSolver<EZ3>::Model &m, Expr &tempPr, Expr &pr)
{
    SMTUtils u1(pr->getFactory());
    // outs () << "Sanity MBP (1): " << isOpX<TRUE>(m.eval(pr)) << "\n";
    assert(isOpX<TRUE>(m.eval(pr)));
    ExprVector args;
    for (auto temp : v) args.push_back(temp->last());
    args.push_back(t);
    // outs () << "Sanity MBP (2): " << (bool)u1.implies(pr, mknary<EXISTS>(args)) << "\n";
    // outs() << "Checking implications: \n";
    // outs() << "cur MBP => z3_qe_model_project_skolem: " << bool(u1.implies(pr, tempPr)) << endl;
    // outs() << "z3_qe_model_project_skolem => cur MBP: " << bool(u1.implies(tempPr, pr)) << endl;
    assert(u1.implies(pr, mknary<EXISTS>(args)));
    assert(u1.implies(pr, tempPr));
    assert(u1.implies(tempPr, pr));
}
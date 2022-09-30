#include <cmath>
#include "ae/BvNormalization.hpp"
#include "ae/ExprBvUtils.hpp"

using namespace ufo;

static inline bool addIsApplicable (Expr exp, Expr eVar) {
    Expr lhs = exp->left();
    Expr rhs = exp->right();
    return isOp<BvUCmp>(exp) && contains(lhs, eVar) && !contains(rhs, eVar);
}

CmpSplitter::CmpSplitter(Expr _exp, Expr var) : exp(_exp), r(exp->right())
{
    assert(isOp<BvUCmp>(exp));
    ExprVector terms;
    getBaddTerm(exp->left(), terms);
    for (auto t: terms) {
        if(contains(t, var))
            xPart.push_back(t);
        else
            yPart.push_back(t);
    }
    this->overflow = !bvTrySquashCoefs(xPart, var);
}

void CmpSplitter::split(splitedCmp& out)
{
    out.exp = exp;
    out.tx = mkbadd(xPart);
    out.y = mkbadd(yPart);
    out.r = r;
    this->nextSplit();
}

void normalizator::run_queue() 
{
    while(!queue.empty()) {
        // pop
        Expr curr = *queue.begin();
        queue.erase(curr);
        Expr lhs = curr->left();
        Expr rhs = curr->right();

        if (!contains(curr, var)) {
            tmpOutSet.insert(curr);
        } else if (contains(rhs, var) && contains(lhs, var)) {
            if (isOpX<BUGE>(curr))
                curr = bvFlipCmp(curr, lhs, rhs);
            CmpSplitter splitter(curr, var);
            ExprSet toQueue;
            bool res = false;

            while (splitter.canSplit()) {
                splitedCmp s;
                splitter.split(s);
                for (auto r : both_rules) {
                    res = r->apply(s, toQueue);
                    if(res) break;
                }
                if(res) break;
            }

            if (!res) {
                // no rule is applicable, abort
                // TODO: backtracking
                set_failed();
                return;
            } else {
                for (auto e : toQueue)
                    enqueue(e);
            }
        } else if (contains(lhs, var)) {
            if (isBmulVar(lhs, var)) {
                tmpOutSet.insert(curr);
                continue;
            } else if (isOpX<BNEG>(lhs)) {
                // apply inv
                Expr next = bvReBuildCmp(curr, mk<BNEG>(rhs), lhs->left());
                if (!isOpX<TRUE>(m.eval(next))) {
                    set_failed();
                    return;
                }
                enqueue(next);
            } else {
                ExprSet toQueue;
                bool res = false;

                // firstly, try div rules
                splitedCmp s{curr, NULL, NULL, NULL};
                for (auto r : div_rules)
                    res = r->apply(s, toQueue);

                CmpSplitter splitter(curr, var);
                while (splitter.canSplit() && !res) {
                    splitter.split(s);
                    for (auto r : add_rules)
                        res = r->apply(s, toQueue);
                }

                if (!res) {
                    // no rule is applicable, abort
                    // TODO: backtracking
                    set_failed();
                    return;
                } else {
                    for (auto e : toQueue)
                        enqueue(e);
                }
            }
        } else if (contains(rhs, var)) {
            enqueue(bvFlipCmp(curr, lhs, rhs));
        }
    }
}

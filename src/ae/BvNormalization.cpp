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
    this->overflow = bvTrySquashCoefs(xPart, var);
}

void CmpSplitter::split(splitedCmp& out)
{
    out.exp = exp;
    out.tx = mkbadd(xPart);
    out.y = mkbadd(yPart);
    out.r = r;
    this->nextSplit();
}

// t(x) + y <= r ---> t(x) <= r-y && y <= r
bool add1::apply(splitedCmp cmp, ExprSet &out)
{
    if (!isOpX<BULE>(cmp.exp))
        return false;
    Expr prem1 = mk<BULE>(cmp.tx, mk<BSUB>(cmp.r, cmp.y));
    Expr prem2 = mk<BULE>(cmp.y, cmp.r);
    if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2))) {
        out.insert(prem1);
        out.insert(prem2);
        return true;
    }
    return false;
}

// t(x) + y <= r ---> t(x) <= r-y && -y <= tx
bool add2::apply(splitedCmp cmp, ExprSet &out)
{
    if (!isOpX<BULE>(cmp.exp))
        return false;
    Expr prem1 = mk<BULE>(cmp.tx, mk<BSUB>(cmp.r, cmp.y));
    Expr prem2 = mk<BULE>(mk<BNEG>(cmp.y), cmp.tx);
    if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2))) {
        out.insert(prem1);
        out.insert(prem2);
        return true;
    }
    return false;
}

void normalizator::run_queue() 
{
    while(!queue.empty()) {
        // pop
        Expr curr = *queue.begin();
        queue.erase(curr);
        
        Expr lhs = curr->left();
        Expr rhs = curr->right();

        if (contains(rhs, var) && contains(lhs, var)) {
            // apply both
            // enqueue output
        } else if (contains(lhs, var)) {
            if (isBmulVar(lhs, var)) {
                tmpOutSet.insert(curr);
                continue;
            } else if (isOpX<BNEG>(lhs)) {
                // apply inv
                enqueue(bvReBuildCmp(curr, mk<BNEG>(rhs), lhs->left()));
            } else {
                CmpSplitter splitter(curr, var);
                ExprSet toQueue;
                bool res = false;

                while (splitter.canSplit()) {
                    splitedCmp s;
                    splitter.split(s);
                    for (auto r : add_rules) {
                        res = r.apply(s, toQueue);
                        if(res) break;
                    }
                    if(res) break;
                }

                if (!res) {
                    // no rule is applicable, abort
                    set_failed();
                    return;
                } else {
                    for (auto e : toQueue)
                        enqueue(e);
                }
            }
        } else if (contains(rhs, var)) {
            enqueue(bvReBuildCmp(curr, rhs, lhs));
        }
    }
}

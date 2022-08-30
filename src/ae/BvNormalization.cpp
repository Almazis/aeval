#include "ae/BvNormalization.hpp"

using namespace ufo;

static inline bool addIsApplicable (Expr exp, Expr eVar) {
    Expr lhs = exp->left();
    Expr rhs = exp->right();
    return isOp<BvUCmp>(exp) && contains(lhs, eVar) && !contains(rhs, eVar);
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

void normalizator::run_queue(ExprSet& outSet) 
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
                outSet.insert(curr);
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
                    splitter.nextSplit();
                }

                if (!res) {
                    // no add rule is applicable, abort
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

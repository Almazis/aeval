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
    outs() << _exp << std::endl;
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

rw_rule::rw_rule(Expr _var, ZSolver<EZ3>::Model& _m) :
    var(_var), efac(var->getFactory()), m(_m), bvSize(getBvSize(var)) {};

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

// t(x) + y <= r ---> -y <= t(x) && y <= r && y != 0
bool add3::apply(splitedCmp cmp, ExprSet &out)
{
    if (!isOpX<BULE>(cmp.exp))
        return false;

    Expr prem1 = mk<BULE>(mk<BNEG>(cmp.y), cmp.tx);
    Expr prem2 = mk<BULE>(cmp.y, cmp.r);
    Expr prem3 = mk<BUGE>(cmp.y, bv::bvnum(1, bvSize, efac));
    if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)) && isOpX<TRUE>(m.eval(prem3)))
    {
        out.insert(prem1);
        out.insert(prem2);
        out.insert(prem3);
        return true;
    }
    return false;
}

// t(x) + y >= r ---> t(x) >= r-y && r <= y-1
bool add4::apply(splitedCmp cmp, ExprSet &out)
{
    if (!isOpX<BUGE>(cmp.exp))
        return false;

    Expr prem1 = mk<BUGE>(cmp.tx, mk<BSUB>(cmp.r, cmp.y));
    Expr prem2 = mk<BULE>(cmp.r, mk<BSUB>(cmp.y, bv::bvnum(1, bvSize, efac)));

    if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
    {
        out.insert(prem1);
        out.insert(prem2);
        return true;
    }
    return false;
}

// t(x) + y >= r ---> t(x) >= r - y && t(x) <= -y -1 && y != 0
bool add5::apply(splitedCmp cmp, ExprSet &out)
{
    if (!isOpX<BUGE>(cmp.exp))
        return false;

    Expr prem1 = mk<BUGE>(cmp.tx, cmp.r);
    Expr prem2 = mk<BULE>(cmp.tx, mk<BSUB>(
        mk<BNEG>(cmp.y),  bv::bvnum(1, bvSize, efac)));
    Expr prem3 = mk<BUGE>(cmp.y, bv::bvnum(1, bvSize, efac));
    if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)) && isOpX<TRUE>(m.eval(prem3)))
    {
        out.insert(prem1);
        out.insert(prem2);
        out.insert(prem3);
        return true;
    }
    return false;
}

// t(x) + y >= r ---> y = 0 && r <= t(x)
bool add6::apply(splitedCmp cmp, ExprSet &out)
{
    if (!isOpX<BUGE>(cmp.exp))
        return false;

    Expr prem1 = mk<EQ>(cmp.y, bv::bvnum(0, bvSize, efac));
    Expr prem2 = mk<BULE>(cmp.r, cmp.tx);
    if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
    {
        out.insert(prem1);
        out.insert(prem2);
        return true;
    }
    return false;
}

// t(x) + y >= r ---> y != 0 && r <= y - 1 && t(x) <= -y-1
bool add7::apply(splitedCmp cmp, ExprSet &out)
{
    if (!isOpX<BUGE>(cmp.exp))
        return false;

    Expr prem1 = mk<BUGE>(cmp.y, bv::bvnum(1, bvSize, efac));
    Expr prem2 = mk<BULE>(cmp.r, mk<BSUB>(cmp.y, bv::bvnum(1, bvSize, efac)));
    Expr prem3 = mk<BULE>(cmp.tx, mk<BSUB>(
        mk<BNEG>(cmp.y), bv::bvnum(1, bvSize, efac)));
    if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)) && isOpX<TRUE>(m.eval(prem3)))
    {
        out.insert(prem1);
        out.insert(prem2);
        out.insert(prem3);
        return true;
    }
    return false;
}

// t(x) + y <= r(x) ---> y <= r(x)-t(x) && t(x) <= r(x)
bool both1::apply(splitedCmp cmp, ExprSet &out)
{
    if (!isOpX<BULE>(cmp.exp))
        return false;
    Expr prem1 = mk<BULE>(cmp.y, mk<BSUB>(cmp.r, cmp.tx));
    Expr prem2 = mk<BULE>(cmp.tx, cmp.r);
    if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
    {
        out.insert(prem1);
        out.insert(prem2);
        return true;
    }
    return false;    
}

// t(x) + y <= r(x) ---> y <= r(x)-t(x) && -t(x) <= y
bool both2::apply(splitedCmp cmp, ExprSet &out)
{
    if (!isOpX<BULE>(cmp.exp))
        return false;
    Expr prem1 = mk<BULE>(cmp.y, mk<BSUB>(cmp.r, cmp.tx));
    Expr prem2 = mk<BULE>(mk<BNEG>(cmp.tx), cmp.y);
    if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
    {
        out.insert(prem1);
        out.insert(prem2);
        return true;
    }
    return false;     
}

// t(x) + y <= r(x) ---> -t(x) <= y && t(x) <= r(x) && t(x) != 0
bool both3::apply(splitedCmp cmp, ExprSet &out)
{
    if (!isOpX<BULE>(cmp.exp))
        return false;
    Expr prem1 = mk<BULE>(mk<BNEG>(cmp.tx), cmp.y);
    Expr prem2 = mk<BULE>(cmp.tx, cmp.r);
    Expr prem3 = mk<BUGE>(cmp.tx, bv::bvnum(1, bvSize, efac));
    if (isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)) && isOpX<TRUE>(m.eval(prem3)))
    {
        out.insert(prem1);
        out.insert(prem2);
        out.insert(prem3);
        return true;
    }
    return false;     
}

// k1 * x <= k2 * x ---> x <= (2^n * k2) / k1
bool both4::apply(splitedCmp cmp, ExprSet &out)
{
    if (!isOpX<BULE>(cmp.exp))
        return false;
    if(!isBmulVar(cmp.exp->left(), var) || !isBmulVar(cmp.exp->right(), var))
        return false;

    int c = pow(2, bvSize);
    Expr k1 = getBmulVar(cmp.exp->left(), var);
    Expr k2 = getBmulVar(cmp.exp->right(), var);
    Expr r = mk<BUDIV>(mk<BMUL>(bv::bvnum(c, bvSize, efac), k2), k1);
    Expr prem1 =  mk<BULE>(var, r);
    if(isOpX<TRUE>(m.eval(prem1)))
    {
        out.insert(prem1);
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
        outs() << curr << std::endl;
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
                    res = r.apply(s, toQueue);
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

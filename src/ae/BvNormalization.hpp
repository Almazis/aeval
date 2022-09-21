#ifndef BVNORM__HPP__
#define BVNORM__HPP__
#include "ufo/Smt/EZ3.hh"
#include "ae/ExprBvUtils.hpp"

using namespace ufo;

// a split of the comparison to the form (tx + y) < r (for <, <=, >, >=)
struct splitedCmp {
    Expr exp; // original expression
    Expr tx;  // term, contains the var
    Expr y;   // term, does not contain the var
    Expr r;   // rhs, may or may not contain the var
};

class CmpSplitter {
    Expr exp;
    ExprVector xPart;
    ExprVector yPart;
    Expr r;
    bool overflow;
public:
    CmpSplitter(Expr _exp, Expr var);

    bool canSplit() {return (!overflow && yPart.size() > 0);} // use before next split

    void nextSplit() {
        Expr tmp = yPart.back ();
        yPart.pop_back();
        xPart.push_back(tmp);
    }

    void split(splitedCmp& out);

};

class rw_rule {
protected:
    Expr var;
    ExprFactory& efac;
    ZSolver<EZ3>::Model& m;
    int bvSize;
public:
    rw_rule(Expr _var, ZSolver<EZ3>::Model& _m)  :
        var(_var), efac(var->getFactory()), m(_m), bvSize(getBvSize(var)) {};
    
    virtual ~rw_rule() {};
    /**
     * @brief returns true if the rule can be applied to the expression 
     * of the form (tx + y) < r (for operations <, <=, >, >=)
     * 
     * @tx: 
     * @out: output for produced premises
     */
    virtual bool apply(splitedCmp cmp, ExprSet &out) = 0;
};


class add1 : public rw_rule {
public:
    add1(Expr _var, ZSolver<EZ3>::Model& _m) : rw_rule(_var, _m) {};

    // t(x) + y <= r ---> t(x) <= r-y && y <= r
    bool apply(splitedCmp cmp, ExprSet &out) override {
        if (!isOpX<BULE>(cmp.exp))
            return false;
        Expr prem1 = mk<BULE>(cmp.tx, mk<BSUB>(cmp.r, cmp.y));
        Expr prem2 = mk<BULE>(cmp.y, cmp.r);
        if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2))) {
            // outs() << "Applied add1\n";
            out.insert(prem1);
            out.insert(prem2);
            return true;
        }
        return false;
    }
};

class add2 : public rw_rule {
public:
    add2(Expr _var, ZSolver<EZ3>::Model& _m) : rw_rule(_var, _m) {};

    // t(x) + y <= r ---> t(x) <= r-y && -y <= tx
    bool apply(splitedCmp cmp, ExprSet &out) override {
        if (!isOpX<BULE>(cmp.exp))
            return false;
        Expr prem1 = mk<BULE>(cmp.tx, mk<BSUB>(cmp.r, cmp.y));
        Expr prem2 = mk<BULE>(mk<BNEG>(cmp.y), cmp.tx);
        if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2))) {
            // outs() << "Applied add2\n";
            out.insert(prem1);
            out.insert(prem2);
            return true;
        }
        return false;
    }
};

class add3 : public rw_rule {
public:
    add3(Expr _var, ZSolver<EZ3>::Model& _m) : rw_rule(_var, _m) {};
 
    // t(x) + y <= r ---> -y <= t(x) && y <= r && y != 0
    bool apply(splitedCmp cmp, ExprSet &out) override {
        if (!isOpX<BULE>(cmp.exp))
            return false;

        Expr prem1 = mk<BULE>(mk<BNEG>(cmp.y), cmp.tx);
        Expr prem2 = mk<BULE>(cmp.y, cmp.r);
        Expr prem3 = mk<BUGE>(cmp.y, bv::bvnum(1, bvSize, efac));
        if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)) && isOpX<TRUE>(m.eval(prem3)))
        {
            // outs() << "Applied add3\n";
            out.insert(prem1);
            out.insert(prem2);
            out.insert(prem3);
            return true;
        }
        return false;
    }
};

class add4 : public rw_rule {
public:
    add4(Expr _var, ZSolver<EZ3>::Model& _m) : rw_rule(_var, _m) {};

    // t(x) + y >= r ---> t(x) >= r-y && r <= y-1
    bool apply(splitedCmp cmp, ExprSet &out) override {
        if (!isOpX<BUGE>(cmp.exp))
            return false;

        Expr prem1 = mk<BUGE>(cmp.tx, mk<BSUB>(cmp.r, cmp.y));
        Expr prem2 = mk<BULE>(cmp.r, mk<BSUB>(cmp.y, bv::bvnum(1, bvSize, efac)));

        if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
        {
            // outs() << "Applied add4\n";
            out.insert(prem1);
            out.insert(prem2);
            return true;
        }
        return false;
    }
};

class add5 : public rw_rule {
public:
    add5(Expr _var, ZSolver<EZ3>::Model& _m) : rw_rule(_var, _m) {};

    // t(x) + y >= r ---> t(x) >= r - y && t(x) <= -y -1 && y != 0
    bool apply(splitedCmp cmp, ExprSet &out) override {
        if (!isOpX<BUGE>(cmp.exp))
            return false;

        Expr prem1 = mk<BUGE>(cmp.tx, cmp.r);
        Expr prem2 = mk<BULE>(cmp.tx, mk<BSUB>(
            mk<BNEG>(cmp.y),  bv::bvnum(1, bvSize, efac)));
        Expr prem3 = mk<BUGE>(cmp.y, bv::bvnum(1, bvSize, efac));
        if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)) && isOpX<TRUE>(m.eval(prem3)))
        {
            // outs() << "Applied add5\n";
            out.insert(prem1);
            out.insert(prem2);
            out.insert(prem3);
            return true;
        }
        return false;
    }
};

class add6 : public rw_rule {
public:
    add6(Expr _var, ZSolver<EZ3>::Model& _m) : rw_rule(_var, _m) {};

    // t(x) + y >= r ---> y = 0 && r <= t(x)
    bool apply(splitedCmp cmp, ExprSet &out) override {
        if (!isOpX<BUGE>(cmp.exp))
            return false;

        Expr prem1 = mk<BULE>(cmp.y, bv::bvnum(0, bvSize, efac));
        Expr prem2 = mk<BULE>(cmp.r, cmp.tx);
        if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
        {
            // outs() << "Applied add6\n";
            out.insert(prem1);
            out.insert(prem2);
            return true;
        }
        return false;
    }
};

class add7 : public rw_rule {
public:
    add7(Expr _var, ZSolver<EZ3>::Model& _m) : rw_rule(_var, _m) {};

    // t(x) + y >= r ---> y != 0 && r <= y - 1 && t(x) <= -y-1
    bool apply(splitedCmp cmp, ExprSet &out) override {
        if (!isOpX<BUGE>(cmp.exp))
            return false;

        Expr prem1 = mk<BUGE>(cmp.y, bv::bvnum(1, bvSize, efac));
        Expr prem2 = mk<BULE>(cmp.r, mk<BSUB>(cmp.y, bv::bvnum(1, bvSize, efac)));
        Expr prem3 = mk<BULE>(cmp.tx, mk<BSUB>(
            mk<BNEG>(cmp.y), bv::bvnum(1, bvSize, efac)));
        if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)) && isOpX<TRUE>(m.eval(prem3)))
        {
            // outs() << "Applied add7\n";
            out.insert(prem1);
            out.insert(prem2);
            out.insert(prem3);
            return true;
        }
        return false;
    }
};

class both1 : public rw_rule {
public:
    both1(Expr _var, ZSolver<EZ3>::Model& _m) : rw_rule(_var, _m) {};

    // t(x) + y <= r(x) ---> y <= r(x)-t(x) && t(x) <= r(x)
    bool apply(splitedCmp cmp, ExprSet &out) override {
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

};

class both2 : public rw_rule {
public:
    both2(Expr _var, ZSolver<EZ3>::Model& _m) : rw_rule(_var, _m) {};

    // t(x) + y <= r(x) ---> y <= r(x)-t(x) && -t(x) <= y
    bool apply(splitedCmp cmp, ExprSet &out) override {
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
};

class both3 : public rw_rule {
public:
    both3(Expr _var, ZSolver<EZ3>::Model& _m) : rw_rule(_var, _m) {};

    // t(x) + y <= r(x) ---> -t(x) <= y && t(x) <= r(x) && t(x) != 0
    bool apply(splitedCmp cmp, ExprSet &out) override {
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

};

class both4 : public rw_rule {
public:
    both4(Expr _var, ZSolver<EZ3>::Model& _m) : rw_rule(_var, _m) {};

    // k1 * x <= k2 * x ---> x <= (2^n * k2) / k1
    bool apply(splitedCmp cmp, ExprSet &out) override {
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
};

class normalizator {
    bool failed = false;
    Expr var;
    ExprFactory& efac;
    ZSolver<EZ3>::Model& m;
    ExprSet queue; // TODO: not a set
    ExprSet tmpOutSet;
    
    std::vector<rw_rule *> add_rules; // vector of add rules
    std::vector<rw_rule *> both_rules; // vector of both rules

    void enqueue(Expr e) {queue.insert(e);}
    void run_queue();
    void set_failed() {failed = true;}
    void clear_failed() {failed = false;}
public:
    normalizator(Expr _var, ZSolver<EZ3>::Model& _m) :
        var(_var), efac(var->getFactory()), m(_m)
    {
        add_rules.push_back(new add1(_var, _m));
        add_rules.push_back(new add2(_var, _m));
        add_rules.push_back(new add3(_var, _m));
        add_rules.push_back(new add4(_var, _m));
        add_rules.push_back(new add5(_var, _m));
        add_rules.push_back(new add6(_var, _m));
        add_rules.push_back(new add7(_var, _m));

        both_rules.push_back(new both1(_var, _m));
        both_rules.push_back(new both2(_var, _m));
        both_rules.push_back(new both3(_var, _m));
        both_rules.push_back(new both4(_var, _m));   
    };
    
    ~normalizator() {
        for (auto it = add_rules.begin(); it != add_rules.end(); ++it)
            delete *it;
        for (auto it = both_rules.begin(); it != both_rules.end(); ++it)
            delete *it;
        add_rules.clear();
        both_rules.clear();
    }
    
    bool normalize(Expr e, ExprSet& outSet) 
    {
        clear_failed();
        queue.clear();
        tmpOutSet.clear();
        enqueue(e);
        run_queue();
        if (!failed) {
            for (auto a : tmpOutSet) {
                outSet.insert(a);
            }
        }
        return (!failed);
    }
};
#endif

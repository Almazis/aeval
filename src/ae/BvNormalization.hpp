#ifndef BVNORM__HPP__
#define BVNORM__HPP__
#include "ufo/Smt/EZ3.hh"

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

    bool canSplit() {return (!overflow && yPart.size() > 1);}

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
public:
    rw_rule(Expr _var, ZSolver<EZ3>::Model& _m) :
        var(_var), efac(var->getFactory()), m(_m) {};
    rw_rule(const rw_rule & r) :
        var(r.var), efac(var->getFactory()), m(r.m) {};
    
    /**
     * @brief returns true if the rule can be applied to the expression 
     * of the form (tx + y) < r (for operations <, <=, >, >=)
     * 
     * @tx: 
     * @out: output for produced premises
     */
    virtual bool apply(splitedCmp cmp, ExprSet &out) {
        // does nothing for base class
        return true;
    }
};

class add1 : public rw_rule {
public:
    add1(rw_rule r) : rw_rule(r) {};
    bool apply(splitedCmp cmp, ExprSet &out) override;
};

class add2 : public rw_rule {
public:
    add2(rw_rule r) : rw_rule(r) {};
    bool apply(splitedCmp cmp, ExprSet &out) override;
};

// class add3 : public rw_rule {
// public:
//     add3(rw_rule r) : rw_rule(r) {};
//     bool apply(splitedCmp cmp, ExprSet &out) override;
// };

// class add4 : public rw_rule {
// public:
//     add4(rw_rule r) : rw_rule(r) {};
//     bool apply(splitedCmp cmp, ExprSet &out) override;
// };

class normalizator {
    bool failed = false;
    Expr var;
    ExprFactory& efac;
    ZSolver<EZ3>::Model& m;
    ExprSet queue; // TODO: not a set
    ExprSet tmpOutSet;
    rw_rule dummyRwRule;
    std::vector<rw_rule> add_rules; // vector of add rules

    void enqueue(Expr e) {queue.insert(e);}
    void run_queue();
    void set_failed() {failed = true;}
    void clear_failed() {failed = false;}
public:
    normalizator(Expr _var, ZSolver<EZ3>::Model& _m) :
        var(_var), efac(var->getFactory()), m(_m), dummyRwRule(var, m) 
    {
        add_rules.push_back(add1(dummyRwRule));
        add_rules.push_back(add2(dummyRwRule));
        // add_rules.push_back(add3(dummyRwRule));
        // add_rules.push_back(add4(dummyRwRule));
    };
    
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

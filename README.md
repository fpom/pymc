# Python CTL model checker

Given a model (the symbolic representation of the statespace and the transition relation) build an object able to symbolically compute the set of states satistfying a formula (CTL, Fair CTL, wip : ACTL and ARCTL).  

## Requirement
 - `pyddd` [https://github.com/fpom/pyddd](https://github.com/fpom/pyddd)
 - `pytl` [https://github.com/fpom/pytl](https://github.com/fpom/pytl)

## Usage

The symbolic representation of the model must be :
 - a sdd for the state space (see [pyddd](https://github.com/fpom/pyddd))
 - a shom for the precedence relation (see [pyddd](https://github.com/fpom/pyddd))

Instantiated with such symbolic representation, the object can be called with the method check on a formula (represented by a string which will be parsed by [pytl](https://github.com/fpom/pytl) or by a `pytl.Phi` object). 
The method `check` returns the sdd representing the states that satisfy the formula.


Example :

        from pymc import CTL_model_checker, FairCTL_model_checker
        %run -m ecco termites-simpler.rr
        v = model("test",split=False, force=True)
        formula = "AF E(Sd U Fg & Te)"
        CTL_mc = CTL_model_checker(v.g.reachable, v.g.m.pred())
        FairCTL_mc = FairCTL_model_checker(v.g.reachable, v.g.m.pred(),["~Ac"])
        print(v.g.initial<=CTL_mc.check(formula))
        print(v.g.initial<=FairCTL_mc.check(formula))


### CTL

Implement the algorithm of Symbolic Model Checking, McMillan 1993, section 2.4.

Supports the operators :
 - unary : `EX, EF, EG, AX, AF, AG`
 - binary : `EU, EW, ER, AU, AW, AR`

### Fair CTL

Implement the algorithm of Symbolic Model Checking, McMillan 1993, section 6.4 and Symbolic model checking: 1020 states and beyond, Burch et al 1992, section 6.2.

The evaluation of the formula is restricter to the trajectoriers verifying fairness constraints of the form `AND([GF f for f in fairness])`.
An additional argument must be given at initialization, representing the fairness constraints :
 - a list of strings, Phi objects or sdd, representing the list of fairness constraints : [f1, f2,...]
 - a single string, Phi or sdd, representing a single fairness constraint

Supports the operators :
 - unary : `EX, EF, EG, AX, AF, AG`
 - binary : `EU, AU`

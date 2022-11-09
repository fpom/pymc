# Python FARCTL symbolic model checker

Given a model (the symbolic representation of the statespace and the transition relation) build an object able to symbolically compute the set of states satistfying an (FAR)CTL formula.  

## Requirement
 - `pyddd` [https://github.com/fpom/pyddd](https://github.com/fpom/pyddd) (Python binding for libDDD)
 - `pytl` [https://github.com/fpom/pytl](https://github.com/fpom/pytl) (Python parser and translator for varied temporal logics)

## Usage

The symbolic representation of the model must be :
 - a sdd for the state space (see [pyddd](https://github.com/fpom/pyddd))
 - a shom (for CTL) or a dict linking list of label strings to shoms (for (F)ARCTL) for the precedence relation (see [pyddd](https://github.com/fpom/pyddd))

Instantiated with such symbolic representation, the object can be called with the method check on a formula (represented by a string which will be parsed by [pytl](https://github.com/fpom/pytl) or by a `pytl.Phi` object). 
The method `check` returns the sdd representing the states that satisfy the formula.


Example :

        from pymc import CTL_model_checker, FARCTL_model_checker
        %run -m ecco Borana_model_ARCTL.rr
        G = model(compact=False, split=False)
        
        CTL_mc = CTL_model_checker(G.lts.states, G.lts.pred)
        formula_CTL = 'EG(Gr)'
        print(G.lts.init<=CTL_mc.check(formula_CTL))
        
        actions = dict()
        for rule in G.model.spec.rules:
            rname = rule.name()
            if G.model.spec.labels.get(rname):
                labels = [l.strip() for l in G.model.spec.labels[rname].split(",")]
            else:
                labels = []
            labels.append(rname)
            actions[G.lts.tpred[rname]] = labels
        FARCTL_mc = FARCTL_model_checker(G.lts.states, actions)
        formula_FARCTL = '{~("Fb-" | "Wl+")}[WFAIR {"Ig+"}]AF(~Gr)'
        print(G.lts.init<=FARCTL_mc.check(formula_FARCTL))


### FARCTL

The syntax of FARCTL formula is defined by [pytl](https://github.com/fpom/pytl) :
    
    phi ::= "(" phi ")"
         |  "~" phi
         |  quantifier phi
         |  unarymod phi
         |  phi boolop phi
         |  phi binarymod phi
         |  atom

    quantifier ::= ("A" | "E") ("{" actions "}")?
    
    unarymod ::= ("X" | "F" | "G") ("{" actions "}")?
    
    boolop ::= "&" | "|" | "=>" | "<=>"
    
    binarymod ::= ("{" actions "}")? ("U" | "R" | "W" | "M") ("{" actions "}")?
    
    atom ::= /\w+|"[^\"]+"|'[^\']+'/
    
    actions ::= "(" actions ")"
        | "~" actions
        | actions boolop actions
        | atom


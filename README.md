# Python ITS model checker

Given a model (the symbolic representation of the statespace and the transition relation) build an object able to symbolically compute the set of states satistfying a formula (CTL, Fair CTL, wip : ACTL and ARCTL).  


## Requirement
 - `pyddd` [https://github.com/fpom/pyddd](https://github.com/fpom/pyddd)
 - `pytl` [https://github.com/fpom/pytl](https://github.com/fpom/pytl)

## Usage

The symbolic representation of the model must be :
 - a sdd for the state space (see [pyddd](https://github.com/fpom/pyddd))
 - a shom for the precedence relation (see [pyddd](https://github.com/fpom/pyddd))
    
### CTL


### Fair CTL

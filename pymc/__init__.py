"""libDDD-based model-checker for (AR)CTL with(out) fairness
"""

from ddd import ddd, sdd, shom
from tl import parse, Phi
from functools import reduce, lru_cache

# TODO : tau actions

def fixpoint(fonction, start):
    current = start
    previous = None
    while previous != current:
        previous = current
        current = fonction(current)
    return current



####################### CTL #######################

class CTL_model_checker(object):
    """
    Object which can symbolically compute the subset of the universe where a given CTL formula is satisfied.

    Attributes :
    - variables : the list of the variables
    - logic : a string naming the logic

    Methods :
    - check(formula) : returns the sdd representing the subset of the universe where the input formula is satisfied
    - atom(var) : returns the sdd representing the subset of the universe where var is True
    """
    def __init__ (self, universe, pred):
        """
        Input :
        - universe is a sdd representing the state space (for example v.g.reachable)
        - pred is a shom representing the precedence relation (inverse of the transition relation)
        """
        # TODO : mettre en cache les output de phi2sdd ?
        assert isinstance(universe, sdd), "universe must be of type sdd"
        assert isinstance(pred, shom), "pred must be of type shom"

        self.logic = "CTL"

        self.variables = next(iter(universe))[0].vars() # c'est tres sale mais je trouve pas d'autre solution pour l'instant

        self.CTL_True = universe
        self.CTL_False = sdd.empty()
        self.neg = lambda phi : self.CTL_True - phi
        self.gfp = lambda fonction : fixpoint(fonction, self.CTL_True)
        self.lfp = lambda fonction : fixpoint(fonction, self.CTL_False)

        self.EX = pred
        self.deadlock = self.neg(self.EX(self.CTL_True))
        self.EF = lambda phi : self.lfp(lambda Z : phi | self.EX(Z))
        self.EG = lambda phi : self.gfp(lambda Z : phi & (self.EX(Z) | self.deadlock))
        self.EU = lambda phi1, phi2 : self.lfp(lambda Z : phi2 | (phi1 & self.EX(Z)))
        self.EW = lambda phi1, phi2 : self.gfp(lambda Z : phi2 | (phi1 & (self.EX(Z) | self.deadlock)))
        self.ER = lambda phi1, phi2 : self.gfp(lambda Z : phi2 & (phi1 | self.EX(Z) | self.deadlock))
        self.EM = lambda phi1, phi2 : self.lfp(lambda Z : phi2 & (phi1 | self.EX(Z)))

        self.AX = lambda phi : self.EX(self.CTL_True) & self.neg(self.EX(self.neg(phi)))
        self.AF = lambda phi : self.lfp(lambda Z : phi | self.AX(Z))
        self.AG = lambda phi : self.gfp(lambda Z : phi & (self.AX(Z) | self.deadlock))
        self.AU = lambda phi1, phi2 : self.lfp(lambda Z : phi2 | (phi1 & self.AX(Z)))
        self.AW = lambda phi1, phi2 : self.gfp(lambda Z : phi2 | (phi1 & (self.AX(Z) | self.deadlock)))
        self.AR = lambda phi1, phi2 : self.gfp(lambda Z : phi2 & (phi1 | self.AX(Z) | self.deadlock))
        self.AM = lambda phi1, phi2 : self.lfp(lambda Z : phi2 & (phi1 | self.AX(Z)))

        self.unarymod = {"EX" : self.EX, "EF" : self.EF, "EG" : self.EG, "AX" : self.AX, "AF" : self.AF, "AG" : self.AG}
        self.binarymod = {"EU" : self.EU, "ER" : self.ER, "EW" : self.EW, "EM" : self.EM, "AU" : self.AU, "AR" : self.AR, "AW" : self.AW, "AM" : self.AM}

    @lru_cache(maxsize=None) # si la version de python etait 3.9 on pourrait utiliser functools.cache directement
    def atom(self, var):
        """
        Input :
        - var : string

        Output :
        The sdd representing the subset of the universe where var is True.
        """
        assert var in self.variables, var + " is not a variable"
        d = ddd.one()
        for v in reversed(self.variables):
            if v == var :
                d = ddd.from_range(var, 1, 1, d)
            else :
                d = ddd.from_range(v, 0, 1, d)
        return sdd.mkz(d) & self.CTL_True


    # recursive function that builds the sdd along the syntax tree (bottom-up, going-up from the tree leaves)
    def _phi2sdd(self, phi):
        if phi.kind == 'bool':
            assert isinstance(phi.value, bool), repr(phi) + " is of kind bool but its value is not a boolean"
            if phi.value:
                return self.CTL_True
            else:
                return self.CTL_False
        elif phi.kind == 'name':
            return self.atom(phi.value)
        elif phi.kind == 'not':
            return self.neg(self._phi2sdd(phi.children[0]))
        elif phi.kind == 'and':
            return reduce(sdd.__and__, [self._phi2sdd(child) for child in phi.children], self.CTL_True)
        elif phi.kind == 'or':
            return reduce(sdd.__or__, [self._phi2sdd(child) for child in phi.children], self.CTL_False)
        elif phi.kind == 'imply':
          	return self.neg(self._phi2sdd(phi.children[0])) | self._phi2sdd(phi.children[1])
        elif phi.kind == 'iff':
          	return (self._phi2sdd(phi.children[0]) & self._phi2sdd(phi.children[1])) | (self.neg(self._phi2sdd(phi.children[0])) & self.neg(self._phi2sdd(phi.children[1])))
        elif phi.kind in self.unarymod:
            return self.unarymod[phi.kind](self._phi2sdd(phi.children[0]))
        elif phi.kind in self.binarymod:
            return self.binarymod[phi.kind](self._phi2sdd(phi.children[0]), self._phi2sdd(phi.children[1]))
        else:
            raise ValueError(repr(phi) + "is not a " + self.logic + " sub formula")


    def check(self, formula):
        """
        Input :
        - formula : string or tl.Phi object

        Output :
        The sdd representing the subset of the universe where the formula is satisfied.
        """
        assert isinstance(formula , str) or isinstance(formula , Phi), "The formula given in input must be a string or a parsed formula"
        if isinstance(formula , str):
            formula = parse(formula).ctl()
        return self._phi2sdd(formula)



####################### Fair CTL #######################

class FairCTL_model_checker(CTL_model_checker):
    def __init__ (self, universe, pred, fairness):
        """
        Input :
        - universe is a sdd representing the state space (for example v.g.reachable)
        - pred is a shom representing the precedence relation (inverse of the transition relation)
        - fairness is a list of CTL formulae (or sdd) to be used as fairness constraints (the fair trajectory must satisfy and[GF f for f in fairness])
        """
        CTL_model_checker.__init__(self, universe, pred)
        if isinstance(fairness, list):
            pass
        elif isinstance(fairness, (str, sdd, Phi)) :
            fairness = [fairness]
        else:
            raise TypeError("fairness must be a list, a string or a sdd expressing a CTL formula")
        if fairness == []:
            print("The list of fairness constraints is empty, you should use the CTL_model_checker instead")

        def fairness_preprocess(f):
            if isinstance(f, (str, Phi)):
                return CTL_model_checker(universe, pred).check(f)
            elif isinstance(f, sdd):
                return f
            else:
                raise TypeError("Fairness constraints must be CTL formulae or SDD")

        self.fairness = [fairness_preprocess(f) for f in fairness]

        self.EG_fair = lambda phi : self.gfp(lambda Z : phi & (self.deadlock | self.EX(reduce(sdd.__and__ , [self.EU(Z, Z & f) for f in self.fairness], self.CTL_True))))
        CTL_model_checker.__init__(self, self.EG_fair(self.CTL_True), pred)

        # EX, AX, EU, EF, EM do not need to be redefined once universe = EG_fair(True)
        self.EX_fair = self.EX
        self.EF_fair = self.EF
        # self.deadlock and self.CTL_true have changed since the redefinition of the universe into EG_fair(True)
        self.EG_fair = lambda phi : self.gfp(lambda Z : phi & (self.deadlock | self.EX(reduce(sdd.__and__ , [self.EU(Z, Z & f) for f in self.fairness], self.CTL_True))))
        self.EU_fair = self.EU
        self.EW_fair = lambda phi1, phi2 : self.EU_fair(phi1, phi2) | self.EG_fair(phi1)
        self.ER_fair = lambda phi1, phi2 : self.EW_fair(phi2, phi1 & phi2)
        self.EM_fair = self.EM

        self.AX_fair = self.AX
        self.AF_fair = lambda phi : self.neg(self.EG_fair(self.neg(phi)))
        self.AG_fair = lambda phi : self.neg(self.EF_fair(self.neg(phi)))
        self.AU_fair = lambda phi1, phi2 : self.neg(self.EU_fair(self.neg(phi2), self.neg(phi1) & self.neg(phi2))) & self.neg(self.EG_fair(self.neg(phi2)))
        self.AW_fair = lambda phi1, phi2 : self.neg(self.EU_fair(self.neg(phi2), self.neg(phi1) & self.neg(phi2)))
        self.AR_fair = lambda phi1, phi2 : self.AW_fair(phi2, phi1 & phi2)
        self.AM_fair = lambda phi1, phi2 : self.AU_fair(phi2, phi1 & phi2)

        self.unarymod = {"EX" : self.EX_fair, "EF" : self.EF_fair, "EG" : self.EG_fair, "AX" : self.AX_fair, "AF" : self.AF_fair, "AG" : self.AG_fair}
        self.binarymod = {"EU" : self.EU_fair, "ER" : self.ER_fair, "EW" : self.EW_fair, "EM" : self.EM_fair, "AU" : self.AU_fair, "AR" : self.AR_fair, "AW" : self.AW_fair, "AM" : self.AM_fair}



####################### ARCTL #######################


class ARCTL_model_checker(CTL_model_checker):
    def __init__ (self, universe, pred_dict, pred, tau_label="_None"):
        """
        Input :
        - universe is a sdd representing the state space (for example v.g.reachable)
        - pred_dict is a dictionary associating transition label strings to shom representing the precedence relation for this label
        - pred is a shom representing the precedence relation (inverse of the transition relation)
        - tau_label : the label representing invisible actions, or None if no invisible actions
        """
        assert isinstance(pred_dict, dict), "pred_dict must be of type dict"
        assert len(pred_dict) >= 1, "pred_dict must contain at least one element"
        for e in pred_dict : # for each key of the dictionnary
            assert isinstance(e, str), "every key of pred_dict must be of type string"
            assert isinstance(pred_dict[e], shom), "every value of pred_dict must be of type shom"

        self.pred_dict = pred_dict
        if tau_label in pred_dict:
            self.tau_label = tau_label
        else:
            self.tau_label = None
        CTL_model_checker.__init__(self, universe, pred)
        self.logic = "ARCTL"

    def build_pred_alpha(self, alpha):
        if alpha.kind == 'bool':
            assert isinstance(alpha.value, bool), repr(alpha) + " is of kind bool but its value is not a boolean"
            if alpha.value:
                return self.pred
            else:
                return shom.empty()
        elif alpha.kind == 'name':
            return self.pred_dict[alpha.value]
        elif alpha.kind == 'not':
            return shom.__sub__(self.pred, self.build_pred_alpha(alpha.children[0])) # not sure of myself here
        elif alpha.kind =='and':
            return reduce(shom.__and__, [self.build_pred_alpha(child) for child in alpha.children], self.pred)
        elif alpha.kind =='or':
            return reduce(shom.__or__, [self.build_pred_alpha(child) for child in alpha.children], shom.empty())
        else:
            raise ValueError(repr(actions) + "is not an action sub formula")

    def check(self, formula):
        """
        Input :
        - formula : string or tl.Phi object

        Output :
        The sdd representing the subset of the universe where the formula is satisfied.
        """
        assert isinstance(formula , str) or isinstance(formula , Phi), "The formula given in input must be a string or a parsed formula"
        if isinstance(formula , str):
            formula = parse(formula).arctl()
        return self._phi2sdd(formula)

    # recursive function that builds the sdd along the syntax tree (bottom-up, going-up from the tree leaves)
    def _phi2sdd(self, phi):
        if phi.actions:
            pred = self.build_pred_alpha(phi.actions)
            if self.tau_label:
                pred = shom.__or__(pred, self.pred_dict[self.tau.label])# the invisible actions are added to pred
            if phi.kind in self.unarymod:
                return CTL_model_checker(self.CTL_True, pred).unarymod[phi.kind](self._phi2sdd(phi.children[0]))
            elif phi.kind in self.binarymod:
                return CTL_model_checker(self.CTL_True, pred).binarymod[phi.kind](self._phi2sdd(phi.children[0]), self._phi2sdd(phi.children[1]))
        else:
            return CTL_model_checker._phi2sdd(self, phi)



####################### Fair ARCTL #######################

class FairARCTL_model_checker(ARCTL_model_checker, FairCTL_model_checker):
    def __init__ (self, universe, pred_dict, pred, fairness, tau_label="_None"):
        ARCTL_model_checker.__init__(self, universe, pred_dict, pred, tau_label)
        FairCTL_model_checker.__init__ (self, universe, self.pred, fairness)

    # recursive function that builds the sdd along the syntax tree (bottom-up, going-up from the tree leaves)
    def _phi2sdd(self, phi):
        if phi.actions:
            pred = self.build_pred_alpha(phi.actions)
            if self.tau_label:
                pred = shom.__or__(pred, self.pred_dict[self.tau_label])# the invisible actions are added to pred
            if phi.kind in self.unarymod:
                FairCTL_model_checker(self.CTL_True, pred, self.fairness).unarymod[phi.kind](self._phi2sdd(phi.children[0]))
            elif phi.kind in self.binarymod:
                return FairCTL_model_checker(self.CTL_True, pred, self.fairness).binarymod[phi.kind](self._phi2sdd(phi.children[0]), self._phi2sdd(phi.children[1]))
        else:
            return FairCTL_model_checker._phi2sdd(self, phi)

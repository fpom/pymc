"""libDDD-based model-checker for (AR)CTL with(out) fairness
"""

from ddd import ddd, sdd, shom
from pytl import parse, Phi
from functools import reduce, lru_cache

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

    Attributes:
    - variables: the list of the variables
    - logic: a string naming the logic

    Methods:
    - check(formula): returns the sdd representing the subset of the universe where the input formula is satisfied
    - atom(var): returns the sdd representing the subset of the universe where var is True
    """
    def __init__ (self, universe, pred):
        """
        Input:
        - universe is a sdd representing the state space (for example v.g.reachable)
        - pred is a shom representing the precedence relation (inverse of the transition relation)
        """
        # TODO : mettre en cache les output de phi2sdd ?
        assert isinstance(universe, sdd), "universe must be of type sdd"
        assert isinstance(pred, shom), "pred must be of type shom"

        self.logic = "CTL"
        
        if universe:
            self.variables = next(iter(universe))[0].vars() # c'est tres sale mais je trouve pas d'autre solution pour l'instant
        else:
            self.variables = []

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
        Input:
        - var: string

        Output:
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
        - formula: string or tl.Phi object

        Output:
        The sdd representing the subset of the universe where the formula is satisfied.
        """
        assert isinstance(formula , str) or isinstance(formula , Phi), "The formula given in input must be a string or a parsed formula"
        if isinstance(formula , str):
            formula = parse(formula).ctl()
        return self._phi2sdd(formula)


####################### ARCTL #######################


class ARCTL_model_checker(CTL_model_checker):
    def __init__ (self, universe, pred_dict, pred, tau_label="_None"):
        """
        Input:
        - universe is a sdd representing the state space (for example v.g.reachable)
        - pred_dict is a dictionary associating transition label strings to shom representing the precedence relation for this label
        - pred is a shom representing the precedence relation (inverse of the transition relation)
        - tau_label is the label representing invisible actions, or '_None' if no invisible actions
        """
        assert isinstance(pred_dict, dict), "pred_dict must be of type dict"
        assert len(pred_dict) >= 1, "pred_dict must contain at least one element"
        for e in pred_dict: # for each key of the dictionnary
            assert isinstance(e, str), "every key of pred_dict must be of type string"
            assert isinstance(pred_dict[e], shom), "every value of pred_dict must be of type shom"
        self.pred_dict = pred_dict
        if tau_label in pred_dict:
            self.tau_label = tau_label
        else:
            self.tau_label = None
        CTL_model_checker.__init__(self, universe, pred)
        self.logic = "ARCTL"

    def alpha_parse(self, alpha):       
        if alpha.kind == 'bool':
            assert isinstance(alpha.value, bool), repr(alpha) + " is of kind bool but its value is not a boolean"
            if alpha.value:
                return self.EX
            else:
                return shom.empty()
        elif alpha.kind == 'name':
            return self.pred_dict[alpha.value]
        elif alpha.kind == 'not':
            return shom.__sub__(self.EX, self.build_pred_alpha(alpha.children[0])) # not sure of myself here
        elif alpha.kind =='and':
            return reduce(shom.__and__, [self.build_pred_alpha(child) for child in alpha.children], self.EX)
        elif alpha.kind =='or':
            return reduce(shom.__or__, [self.build_pred_alpha(child) for child in alpha.children], shom.empty())
        else:
            raise ValueError(repr(alpha) + "is not an action sub formula")
            
    def build_pred_alpha(self, alpha):
        pred_alpha = self.alpha_parse(alpha)
        if self.tau_label:
                pred_alpha = shom.__or__(pred_alpha, self.pred_dict[self.tau_label])# the invisible actions are added to pred
        return pred_alpha

    def check(self, formula):
        """
        Input :
        - formula: string or tl.Phi object

        Output:
        The sdd representing the subset of the universe where the formula is satisfied.
        """
        assert isinstance(formula , str) or isinstance(formula , Phi), "The formula given in input must be a string or a parsed formula"
        if isinstance(formula , str):
            formula = parse(formula).arctl()
        return self._phi2sdd(formula)

    def _EXevent(self, pred_alpha, event):
        if event.kind == "actions":# \exists_{\alpha \land \Event{\Actions}} \X Z
            return lambda phi : CTL_model_checker(self.CTL_True, pred_alpha & self.build_pred_alpha(event.children[0])).unarymod["EX"](phi)
        else:# \Event{\States} \land (\exists_\alpha \X Z \lor \neg \exists_\alpha \X \top)
            return lambda phi : self._phi2sdd(event) & (CTL_model_checker(self.CTL_True, pred_alpha).unarymod["EX"](phi) | CTL_model_checker(self.CTL_True, pred_alpha).deadlock)
        
    def _EXnotevent(self, pred_alpha, event):
        if event.kind == "actions":# \exists_{\alpha \land \neg\Event{\Actions}} \X Z \lor \neg\exists_\alpha \X \top
            return lambda phi : CTL_model_checker(self.CTL_True, pred_alpha & self.build_pred_alpha(Phi("not", event.children[0]))).unarymod["EX"](phi) | CTL_model_checker(self.CTL_True, pred_alpha).deadlock
        else:# \neg\Event{\States} \land (\exists_\alpha \X Z \lor \neg \exists_\alpha \X \top)
            return lambda phi : self.neg(self._phi2sdd(event)) & (CTL_model_checker(self.CTL_True, pred_alpha).unarymod["EX"](phi) | CTL_model_checker(self.CTL_True, pred_alpha).deadlock)
        
    def _fairunarymod(self, pred, EG_fair):
        mc = CTL_model_checker(EG_fair(self.CTL_True), pred)
        # EX, AX, EF do not need to be redefined once universe = EG_fair(True)
        EX_fair = mc.EX
        EF_fair = mc.EF
        AX_fair = mc.AX
        AF_fair = lambda phi : mc.neg(EG_fair(mc.neg(phi)))
        AG_fair = lambda phi : mc.neg(EF_fair(mc.neg(phi)))
        return {"EX" : EX_fair, "EF" : EF_fair, "EG" : EG_fair, "AX" : AX_fair, "AF" : AF_fair, "AG" : AG_fair}
    
    def _fairbinarymod(self, pred, EG_fair):
        mc = CTL_model_checker(EG_fair(self.CTL_True), pred)
        # EU, EM do not need to be redefined once universe = EG_fair(True)
        EU_fair = mc.EU
        EW_fair = lambda phi1, phi2 : EU_fair(phi1, phi2) | EG_fair(phi1)
        ER_fair = lambda phi1, phi2 : EW_fair(phi2, phi1 & phi2)
        EM_fair = mc.EM  
        AU_fair = lambda phi1, phi2 : mc.neg(EU_fair(mc.neg(phi2), mc.neg(phi1) & mc.neg(phi2))) & mc.neg(EG_fair(mc.neg(phi2)))
        AW_fair = lambda phi1, phi2 : mc.neg(EU_fair(mc.neg(phi2), mc.neg(phi1) & mc.neg(phi2)))
        AR_fair = lambda phi1, phi2 : AW_fair(phi2, phi1 & phi2)
        AM_fair = lambda phi1, phi2 : AU_fair(phi2, phi1 & phi2)
        return {"EU" : EU_fair, "ER" : ER_fair, "EW" : EW_fair, "EM" : EM_fair, "AU" : AU_fair, "AR" : AR_fair, "AW" : AW_fair, "AM" : AM_fair}
        
    # recursive function that builds the sdd along the syntax tree (bottom-up, going-up from the tree leaves)
    def _phi2sdd(self, phi):
        if phi.actions:
            pred = self.build_pred_alpha(phi.actions)
        else:
            pred = self.EX
        if phi.ufair or phi.wfair or phi.sfair:
            for f in phi.sfair:
                assert f.condition.kind != "actions", "Action event not allowed in condition of strong fairness"
            tau_ufair = lambda Z: reduce(sdd.__and__, [CTL_model_checker(self.CTL_True, pred).binarymod["EU"](Z, Z & self._EXevent(pred, f.then)(Z)) for f in phi.ufair], self.CTL_True)
            tau_wfair = lambda Z: reduce(sdd.__and__, [CTL_model_checker(self.CTL_True, pred).binarymod["EU"](Z, Z & (self._EXnotevent(pred, f.condition)(Z) | self._EXevent(pred, f.then)(Z))) for f in phi.wfair], self.CTL_True)
            tau_sfair = lambda Z: reduce(sdd.__and__, [self._EXnotevent(pred, f.condition)(Z) | CTL_model_checker(self.CTL_True, pred).binarymod["EU"](Z, Z & self._EXevent(pred, f.then)(Z)) for f in phi.sfair], self.CTL_True)
            EG_fair = lambda phi: CTL_model_checker(self.CTL_True, pred).binarymod["EU"](phi, self.gfp(lambda Z: phi & tau_ufair(Z) & tau_wfair(Z) & tau_sfair(Z)))
            if not(EG_fair(self.CTL_True)):
                print(f"WARNING: No fair {phi.actions}-path exists for {''.join([f'[UFAIR {f.then}]' for f in phi.ufair])}{''.join([f'[WFAIR {f.condition} THEN {f.then}]' for f in phi.wfair])}{''.join([f'[SFAIR {f.condition} THEN {f.then}]' for f in phi.sfair])}")
            if phi.kind in self.unarymod:
                return self._fairunarymod(pred, EG_fair)[phi.kind](self._phi2sdd(phi.children[0]))
            elif phi.kind in self.binarymod:
                return self._fairbinarymod(pred, EG_fair)[phi.kind](self._phi2sdd(phi.children[0]), self._phi2sdd(phi.children[1]))
            else:
                assert False, "Fairness assumption without quantifier"
        else:
            if phi.kind in self.unarymod:
                return CTL_model_checker(self.CTL_True, pred).unarymod[phi.kind](self._phi2sdd(phi.children[0]))
            elif phi.kind in self.binarymod:
                return CTL_model_checker(self.CTL_True, pred).binarymod[phi.kind](self._phi2sdd(phi.children[0]), self._phi2sdd(phi.children[1]))
            else:
                return CTL_model_checker._phi2sdd(self, phi)

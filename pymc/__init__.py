from ddd import ddd, sdd, shom
from tl import parse, Phi
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
    
    Attributes :
    - variables : the list of the variables
    
    Methods :
    - check(formula) : returns the sdd representing the subset of the universe where the input formula is satisfied
    - atom(var) : returns the sdd representing the subset of the universe where var is True
    """
    def __init__ (self, universe, pred):
        """
        Input :
        - universe is a sdd representing the state space (for example v.g.reachable)
        - pred is a shom representing the inverse of succ (for exemple v.g.m.pred())
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

        self.EX = pred & universe
        self.EF = lambda phi : self.lfp(lambda Z : phi | self.EX(Z))
        self.EG = lambda phi : self.gfp(lambda Z : phi & self.EX(Z))
        self.EU = lambda phi1, phi2 : self.lfp(lambda Z : phi2 | (phi1 & self.EX(Z)))
        self.ER = lambda phi1, phi2 : self.gfp(lambda Z : phi2 & (phi1 | self.EX(Z)))
        self.EW = lambda phi1, phi2 : self.gfp(lambda Z : phi2 | (phi1 & self.EX(Z)))

        # definition of universal operators in term of fix points
        self.AX = lambda phi : self.EX(phi) - self.EX(neg(phi))
        self.AF = lambda phi : self.lfp(lambda Z : phi | self.AX(Z))
        self.AG = lambda phi : self.gfp(lambda Z : phi & self.AX(Z))
        self.AU = lambda phi1, phi2 : self.lfp(lambda Z : phi2 | (phi1 & self.AX(Z)))
        self.AR = lambda phi1, phi2 : self.gfp(lambda Z : phi2 & (phi1 | self.AX(Z)))
        self.AW = lambda phi1, phi2 : self.gfp(lambda Z : phi2 | (phi1 & self.AX(Z)))

        # redefinition of universal operators in term of negation of existential ones
        self.AX = lambda phi : self.neg(self.EX(self.neg(phi))) # /!\ if there is no path from s, then s |= AX(phi) because there is no path that falsifies phi
        self.AF = lambda phi : self.neg(self.EG(self.neg(phi)))
        self.AG = lambda phi : self.neg(self.EF(self.neg(phi)))
        self.AU = lambda phi1, phi2 : self.neg(self.EU(self.neg(phi2),self.neg(phi1) & self.neg(phi2)) | self.EG(self.neg(phi2)))

        self.unarymod = {"EX" : self.EX, "EF" : self.EF, "EG" : self.EG, "AX" : self.AX, "AF" : self.AF, "AG" : self.AG}
        self.binarymod = {"EU" : self.EU, "ER" : self.ER, "EW" : self.EW, "AU" : self.AU, "AR" : self.AR, "AW" : self.AW}

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
        elif phi.kind =='and':
            return reduce(sdd.__and__, [self._phi2sdd(child) for child in phi.children], self.CTL_True)
        elif phi.kind =='or':
            return reduce(sdd.__or__, [self._phi2sdd(child) for child in phi.children], self.CTL_False)
        elif phi.kind in self.unarymod:
            return self.unarymod[phi.kind](self._phi2sdd(phi.children[0]))
        elif phi.kind in self.binarymod:
            return self.binarymod[phi.kind](self._phi2sdd(phi.children[0]), self._phi2sdd(phi.children[1]))
        else:
            raise ValueError(repr(phi) + "is not a " + self.logic + " CTL sub formula")

            
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
        - pred is a shom representing the inverse of succ (for exemple v.g.m.pred())
        - fairness is a list of CTL formulae (or sdd) to be used as fairness constraints (the fair trajectory must satisfy and[GF f for f in fairness])
        """
        super().__init__(universe, pred)
        self.logic = "Fair CTL"
        if isinstance(fairness, list):
            pass
        elif isinstance(fairness, str) or isinstance(fairness, sdd) :
            fairness = [fairness]
        else:
            raise TypeError("fairness must be a list or a string expressing a CTL formula")
        if fairness == []:
            print("The list of fairness constraints is empty, you should used the CTL_model_checker instead")

        def fairness_preprocess(f):
            if isinstance(f, str) or isinstance(f, Phi):
                return CTL_model_checker(universe, pred).check(f)
            elif isinstance(f, sdd):
                return f
            else:
                raise TypeError("Fairness constraints must be CTL formulae or SDD")

        self.fairness = [fairness_preprocess(f) for f in fairness]
        
        # see Symbolic Model Checking, McMillan 1993, section 6.4 or Symbolic model checking: 1020 states and beyond, Burch et al 1992, section 6.2
        self.EG_fair = lambda phi : self.gfp(lambda Z : phi & self.EX(reduce(sdd.__and__ , [self.EU(Z, Z & f) for f in self.fairness], self.CTL_True)))
        self.EG_fair_True = self.EG_fair(self.CTL_True)
        self.EX_fair = lambda phi : self.EX(phi & self.EG_fair_True)
        self.EF_fair = lambda phi : self.EF(phi & self.EG_fair_True)
        self.EU_fair = lambda phi1, phi2 : self.EU(phi1, phi2 & self.EG_fair_True)

        # definition of universal operators as negation of existential ones (not sure of myself here)
        self.AX_fair = lambda phi : self.neg(self.EX_fair(self.neg(phi)))
        self.AF_fair = lambda phi : self.neg(self.EG_fair(self.neg(phi)))
        self.AG_fair = lambda phi : self.neg(self.EF_fair(self.neg(phi)))
        self.AU_fair = lambda phi1, phi2 : self.neg(self.EU_fair(self.neg(phi2), self.neg(phi1) & self.neg(phi2)) | self.EG_fair(self.neg(phi2)))

        self.unarymod = {"EX" : self.EX_fair, "EF" : self.EF_fair, "EG" : self.EG_fair, "AX" : self.AX_fair, "AF" : self.AF_fair, "AG" : self.AG_fair}
        self.binarymod = {"EU" : self.EU_fair, "AU" : self.AU_fair}#, "ER" : ER, "EW" : EW, "AR" : AR, "AW" : AW}


        
####################### ACTL #######################
        
class ACTL_model_checker(CTL_model_checker):
    pass

  

####################### ARCTL #######################

class ARCTL_model_checker(CTL_model_checker):
    pass

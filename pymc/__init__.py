"""
libDDD-based model-checker for (AR)CTL with(out) fairness
"""

from ddd import ddd, sdd, shom
from tl import parse, Phi
from functools import reduce
from ast import literal_eval

try:
    # Python >= 3.9
    from functools import cache
except ImportError:
    # Python < 3.9
    from functools import lru_cache

    cache = lru_cache(maxsize=None)


def fixpoint(fonction, start):
    current = start
    previous = None
    while previous != current:
        previous = current
        current = fonction(current)
    return current


#
# CTL
#


class CTL_model_checker:
    """
    Object which can symbolically compute the subset of the universe where a
    given CTL formula is satisfied.

    Attributes:
    - variables: the list of the variables
    - logic: a string naming the logic

    Methods:
    - check(formula): returns the sdd representing the subset of the universe
      where the input formula is satisfied
    """

    def __init__(self, universe, pred, atom=None):
        """
        Input:
        - universe is a sdd representing the state space
        - pred is a shom representing the precedence relation
          (inverse of the transition relation)
        - atom: a function that translates an atom into a sdd, if None is
          given, a default method is used
        """
        if not isinstance(universe, sdd):
            raise TypeError("universe must be of type sdd")
        if not isinstance(pred, shom):
            raise TypeError("pred must be of type shom")
        self.logic = "CTL"
        if universe:
            # ugly, should be changed if sdd are fully used
            self.variables = next(iter(universe))[0].vars()
        else:
            # the universe is empty when checking when checking a fairness
            # assumption that no path satisfy
            self.variables = []
        if atom is None:
            self.atom = cache(self._atom)
        else:
            self.atom = cache(atom)
        self._atom_arg = atom
        self.CTL_True = universe
        self.CTL_False = sdd.empty()
        self.neg = lambda phi: self.CTL_True - phi
        self.gfp = lambda fonction: fixpoint(fonction, self.CTL_True)
        self.lfp = lambda fonction: fixpoint(fonction, self.CTL_False)
        self.EX = pred
        self.deadlock = self.neg(self.EX(self.CTL_True))
        self.EF = lambda phi: self.lfp(lambda Z: phi | self.EX(Z))
        self.EG = lambda phi: self.gfp(lambda Z: phi & (self.EX(Z) | self.deadlock))
        self.EU = lambda phi1, phi2: self.lfp(lambda Z: phi2 | (phi1 & self.EX(Z)))
        self.EW = lambda phi1, phi2: self.gfp(
            lambda Z: phi2 | (phi1 & (self.EX(Z) | self.deadlock))
        )
        self.ER = lambda phi1, phi2: self.gfp(
            lambda Z: phi2 & (phi1 | self.EX(Z) | self.deadlock)
        )
        self.EM = lambda phi1, phi2: self.lfp(lambda Z: phi2 & (phi1 | self.EX(Z)))
        self.AX = lambda phi: (
            self.EX(self.CTL_True) & self.neg(self.EX(self.neg(phi)))
        )
        self.AF = lambda phi: self.lfp(lambda Z: phi | self.AX(Z))
        self.AG = lambda phi: self.gfp(lambda Z: phi & (self.AX(Z) | self.deadlock))
        self.AU = lambda phi1, phi2: self.lfp(lambda Z: phi2 | (phi1 & self.AX(Z)))
        self.AW = lambda phi1, phi2: self.gfp(
            lambda Z: phi2 | (phi1 & (self.AX(Z) | self.deadlock))
        )
        self.AR = lambda phi1, phi2: self.gfp(
            lambda Z: phi2 & (phi1 | self.AX(Z) | self.deadlock)
        )
        self.AM = lambda phi1, phi2: self.lfp(lambda Z: phi2 & (phi1 | self.AX(Z)))
        self.unarymod = {
            "EX": self.EX,
            "EF": self.EF,
            "EG": self.EG,
            "AX": self.AX,
            "AF": self.AF,
            "AG": self.AG,
        }
        self.binarymod = {
            "EU": self.EU,
            "ER": self.ER,
            "EW": self.EW,
            "EM": self.EM,
            "AU": self.AU,
            "AR": self.AR,
            "AW": self.AW,
            "AM": self.AM,
        }

    def _atom(self, var):
        """
        Input:
        - var: string

        Output:
        The sdd representing the subset of the universe where var is True.
        """
        if var[-1] == "+" or var[-1] == "-":
            if var[:-1] not in self.variables:
                raise ValueError(f"{var[:-1]} is not a variable")
            value = int(var[-1] == "+")
            var = var[:-1]
        else:
            if var not in self.variables:
                raise ValueError(f"{var} is not a variable")
            value = 1
        d = ddd.one()
        for v in reversed(self.variables):
            if v == var:
                d = ddd.from_range(var, value, value, d)
            else:
                d = ddd.from_range(v, 0, 1, d)
        return sdd.mkz(d) & self.CTL_True

    # recursive function that builds the sdd along the syntax tree
    # (bottom-up, going-up from the tree leaves)
    def _phi2sdd(self, phi):
        if phi.kind == "bool":
            if not isinstance(phi.value, bool):
                raise TypeError(
                    f"{phi!r} is of kind bool" f" but its value is not a boolean"
                )
            if phi.value:
                return self.CTL_True
            else:
                return self.CTL_False
        elif phi.kind == "name":
            return self.atom(phi.value)
        elif phi.kind == "not":
            return self.neg(self._phi2sdd(phi.children[0]))
        elif phi.kind == "and":
            return reduce(
                sdd.__and__,
                [self._phi2sdd(child) for child in phi.children],
                self.CTL_True,
            )
        elif phi.kind == "or":
            return reduce(
                sdd.__or__,
                [self._phi2sdd(child) for child in phi.children],
                self.CTL_False,
            )
        elif phi.kind == "imply":
            return self.neg(self._phi2sdd(phi.children[0])) | self._phi2sdd(
                phi.children[1]
            )
        elif phi.kind == "iff":
            return (self._phi2sdd(phi.children[0]) & self._phi2sdd(phi.children[1])) | (
                self.neg(self._phi2sdd(phi.children[0]))
                & self.neg(self._phi2sdd(phi.children[1]))
            )
        elif phi.kind in self.unarymod:
            return self.unarymod[phi.kind](self._phi2sdd(phi.children[0]))
        elif phi.kind in self.binarymod:
            return self.binarymod[phi.kind](
                self._phi2sdd(phi.children[0]), self._phi2sdd(phi.children[1])
            )
        else:
            raise ValueError(f"{phi!r} is not a {self.logic} sub-formula")

    def check(self, formula):
        """
        Input:
        - formula: string or tl.Phi object

        Output:
        The sdd representing the subset of the universe where the formula
        is satisfied.
        """
        if not isinstance(formula, (str, Phi)):
            raise TypeError(
                "The formula given in input must be a string" " or a parsed formula"
            )
        if isinstance(formula, str):
            formula = parse(formula).ctl()
        return self._phi2sdd(formula)


#
# FARCTL
#


class FARCTL_model_checker(CTL_model_checker):
    def __init__(self, universe, actions, tau_label="_None", atom=None):
        """
        Input:
        - universe is a sdd representing the state space
        - actions is a dict associating shoms to lists of label strings
        - tau_label is the label representing invisible actions,
          or '_None' if no invisible actions
        - atom is like for CTL_model_checker
        """
        if not isinstance(actions, dict):
            raise TypeError("actions must be of type dict")
        if len(actions) < 1:
            raise ValueError("actions must contain at least one element")
        self.actions = actions
        self.action_labels = set()
        for action, labels in self.actions.items():
            if not isinstance(action, shom):
                raise TypeError("the key of every item of action must be of type shom")
            if isinstance(labels, str):
                labels = [labels]
            elif not isinstance(labels, (list, tuple)):
                raise ValueError(
                    "the value of every item of action must be of type list"
                )
            for lbl in labels:
                if not (isinstance(lbl, str)):
                    raise TypeError(
                        "the value of every item of action must be a list of strings"
                    )
                self.action_labels.add(lbl)
        self.action_labels = list(self.action_labels)
        if tau_label in self.action_labels:
            self.tau_label = tau_label
        else:
            self.tau_label = None
        super().__init__(universe, reduce(shom.__or__, self.actions), atom)
        self.logic = "FARCTL"

    def alpha_parse(self, alpha, labels):
        if self.tau_label in labels:
            return True
        elif alpha.kind == "bool":
            if not isinstance(alpha.value, bool):
                raise TypeError(
                    f"{alpha!r} is of kind bool but its value" " is not a boolean"
                )
            return alpha.value
        elif alpha.kind == "name":
            if alpha.value not in self.action_labels:
                raise ValueError(f"{alpha.value} is not an action label")
            return alpha.value in labels
        elif alpha.kind == "not":
            return not self.alpha_parse(alpha.children[0], labels)
        elif alpha.kind == "and":
            return reduce(
                bool.__and__,
                [self.alpha_parse(child, labels) for child in alpha.children],
                True,
            )
        elif alpha.kind == "or":
            return reduce(
                bool.__or__,
                [self.alpha_parse(child, labels) for child in alpha.children],
                False,
            )
        else:
            raise ValueError(f"{alpha!r} is not an action sub formula")

    # TODO: put the result of build_pred_alpha in cache in order to prevent
    # computing again a pred already known, I cannot do it easily because Phi
    # are not hashable
    def build_pred_alpha(self, alpha):
        return reduce(
            shom.__or__,
            [
                action
                for (action, labels) in self.actions.items()
                if self.alpha_parse(alpha, labels)
            ],
            shom.empty(),
        )

    def check(self, formula):
        """
        Input:
        - formula: string or tl.Phi object

        Output:
        The sdd representing the subset of the universe where the formula
        is satisfied.
        """
        if not isinstance(formula, (str, Phi)):
            raise TypeError(
                "The formula given in input must be a string" " or a parsed formula"
            )
        if isinstance(formula, str):
            formula = parse(formula).arctl()
        return self._phi2sdd(formula)

    def _EXevent(self, alpha, event):
        if event.kind == "actions":
            # \exists_{\alpha \land \Event{\Actions}} \X Z
            pr = self.build_pred_alpha(Phi("and", alpha, event.children[0]))
            mc = CTL_model_checker(self.CTL_True, pr, self._atom_arg)
            return lambda phi: mc.unarymod["EX"](phi)
        else:
            # \Event{\States} \land (\exists_\alpha \X Z
            #    \lor \neg \exists_\alpha \X \top)
            mc = CTL_model_checker(
                self.CTL_True, self.build_pred_alpha(alpha), self._atom_arg
            )
            return lambda phi: (
                self._phi2sdd(event) & (mc.unarymod["EX"](phi) | mc.deadlock)
            )

    def _EXnotevent(self, alpha, event):
        if event.kind == "actions":
            # \exists_{\alpha \land \neg\Event{\Actions}} \X Z
            #    \lor \neg\exists_\alpha \X \top
            pr1 = self.build_pred_alpha(
                Phi("and", alpha, Phi("not", event.children[0]))
            )
            mc1 = CTL_model_checker(self.CTL_True, pr1, self._atom_arg)
            pr2 = self.build_pred_alpha(alpha)
            mc2 = CTL_model_checker(self.CTL_True, pr2)
            return lambda phi: mc1.unarymod["EX"](phi) | mc2.deadlock
        else:
            # \neg\Event{\States} \land (\exists_\alpha \X Z
            #    \lor \neg \exists_\alpha \X \top)
            pr = self.build_pred_alpha(alpha)
            mc = CTL_model_checker(self.CTL_True, pr)
            return lambda phi: (
                self.neg(self._phi2sdd(event)) & (mc.unarymod["EX"](phi) | mc.deadlock)
            )

    def _fairunarymod(self, pred, EG_fair):
        mc = CTL_model_checker(EG_fair(self.CTL_True), pred)
        # EX, AX, EF do not need to be redefined once universe = EG_fair(True)
        EX_fair = mc.EX
        EF_fair = mc.EF
        AX_fair = mc.AX
        AF_fair = lambda phi: mc.neg(EG_fair(mc.neg(phi)))
        AG_fair = lambda phi: mc.neg(EF_fair(mc.neg(phi)))
        return {
            "EX": EX_fair,
            "EF": EF_fair,
            "EG": EG_fair,
            "AX": AX_fair,
            "AF": AF_fair,
            "AG": AG_fair,
        }

    def _fairbinarymod(self, pred, EG_fair):
        mc = CTL_model_checker(EG_fair(self.CTL_True), pred)
        # EU, EM do not need to be redefined once universe = EG_fair(True)
        EU_fair = mc.EU
        EW_fair = lambda phi1, phi2: EU_fair(phi1, phi2) | EG_fair(phi1)
        ER_fair = lambda phi1, phi2: EW_fair(phi2, phi1 & phi2)
        EM_fair = mc.EM
        AU_fair = lambda phi1, phi2: mc.neg(
            EU_fair(mc.neg(phi2), mc.neg(phi1) & mc.neg(phi2))
        ) & mc.neg(EG_fair(mc.neg(phi2)))
        AW_fair = lambda phi1, phi2: mc.neg(
            EU_fair(mc.neg(phi2), mc.neg(phi1) & mc.neg(phi2))
        )
        AR_fair = lambda phi1, phi2: AW_fair(phi2, phi1 & phi2)
        AM_fair = lambda phi1, phi2: AU_fair(phi2, phi1 & phi2)
        return {
            "EU": EU_fair,
            "ER": ER_fair,
            "EW": EW_fair,
            "EM": EM_fair,
            "AU": AU_fair,
            "AR": AR_fair,
            "AW": AW_fair,
            "AM": AM_fair,
        }

    # recursive function that builds the sdd along the syntax tree
    # (bottom-up, going-up from the tree leaves)
    def _phi2sdd(self, phi):
        if phi.actions:
            pred = self.build_pred_alpha(phi.actions)
            alpha = phi.actions
        else:
            pred = self.EX
            alpha = Phi("bool", value=True)
        if phi.ufair or phi.wfair or phi.sfair:
            for f in phi.sfair:
                if f.condition.kind != "actions":
                    raise ValueError(
                        "Action event not allowed in condition" " of strong fairness"
                    )

            def tau_ufair(Z):
                items = [
                    CTL_model_checker(self.CTL_True, pred).binarymod["EU"](
                        Z, Z & self._EXevent(alpha, f.then)(Z)
                    )
                    for f in phi.ufair
                ]
                return reduce(sdd.__and__, items, self.CTL_True)

            def tau_wfair(Z):
                items = [
                    CTL_model_checker(self.CTL_True, pred).binarymod["EU"](
                        Z,
                        Z
                        & (
                            self._EXnotevent(alpha, f.condition)(Z)
                            | self._EXevent(alpha, f.then)(Z)
                        ),
                    )
                    for f in phi.wfair
                ]
                return reduce(sdd.__and__, items, self.CTL_True)

            def tau_sfair(Z):
                items = [
                    self._EXnotevent(alpha, f.condition)(Z)
                    | CTL_model_checker(self.CTL_True, pred).binarymod["EU"](
                        Z, Z & self._EXevent(alpha, f.then)(Z)
                    )
                    for f in phi.sfair
                ]
                return reduce(sdd.__and__, items, self.CTL_True)

            EG_fair = lambda phi: (
                CTL_model_checker(self.CTL_True, pred).binarymod["EU"](
                    phi,
                    self.gfp(
                        lambda Z: phi & tau_ufair(Z) & tau_wfair(Z) & tau_sfair(Z)
                    ),
                )
            )
            if not EG_fair(self.CTL_True):
                print(
                    f"WARNING: No fair {phi.actions}-path exists for {''.join([f'[UFAIR {f.then}]' for f in phi.ufair])}{''.join([f'[WFAIR {f.condition} THEN {f.then}]' for f in phi.wfair])}{''.join([f'[SFAIR {f.condition} THEN {f.then}]' for f in phi.sfair])}"
                )
            if phi.kind in self.unarymod:
                fun = self._fairunarymod(pred, EG_fair)[phi.kind]
                return fun(self._phi2sdd(phi.children[0]))
            elif phi.kind in self.binarymod:
                fun = self._fairbinarymod(pred, EG_fair)[phi.kind]
                return fun(
                    self._phi2sdd(phi.children[0]), self._phi2sdd(phi.children[1])
                )
            else:
                raise ValueError("Fairness assumption without quantifier")
        else:
            if phi.kind in self.unarymod:
                mc = CTL_model_checker(self.CTL_True, pred).unarymod[phi.kind]
                return mc(self._phi2sdd(phi.children[0]))
            elif phi.kind in self.binarymod:
                mc = CTL_model_checker(self.CTL_True, pred).binarymod[phi.kind]
                return (self._phi2sdd(phi.children[0]), self._phi2sdd(phi.children[1]))
            else:
                return CTL_model_checker._phi2sdd(self, phi)

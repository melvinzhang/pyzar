# ---------------------------------------------------------------------------
# Stage 3C -- substitute-internal representability proofs.
#
# This layer sits above ``hf_logic``.  The raw syntax/formula definitions live
# in ``hf_repr_core.py``; the object-level proof constructors needed to prove
# the internal graph rules live in ``hf_logic.py`` and therefore cannot be
# imported by core without a cycle.
# ---------------------------------------------------------------------------

from fusion import ASSUME
from proof import proof
from tactics import (
    SPEC,
    SPECL,
    SYM,
    MP,
    DISJ1,
    DISJ2,
    NOT_INTRO,
    DISCH,
    NOT_ELIM,
    EQT_ELIM,
    CONJ,
)
from hf_syntax import (
    IS_TERM_AT_VAR,
    SUBSTITUTE_AT_EMPTY,
    SUBSTITUTE_AT_VAR_HIT,
    SUBSTITUTE_AT_VAR_MISS,
)
from hf_repr_core import (
    IS_TERM_EMPTY,
    TEMPLATE_FILL_INTERNAL_DEF,
    TEMPLATE_FILL_EQ_SUBSTITUTE_TERM,
    SUBSTITUTE_INTERNAL_EQUIV,
    _SUBST_RULE_EMPTY,
    _SUBST_RULE_VAR_HIT,
    _SUBST_RULE_VAR_MISS,
    _SUBST_RULE_INSERT,
    _SUBST_RULE_EQ,
    _SUBST_RULE_IN,
    _SUBST_RULE_NOT,
    _SUBST_RULE_IMP,
    _SUBST_RULE_FORALL_HIT,
    _SUBST_RULE_FORALL_MISS,
    _SUBST_HEADLINE_SYNTACTIC,
    _prov_substitute_internal_rel,
    _prov_template_fill_internal_rel,
)


_SUBST_GRAPH_NOT_ELIM = (
    f"!phi t v phi_r. "
    f"{_prov_substitute_internal_rel('Not_f phi', 't', 'v', 'Not_f phi_r')} ==> "
    f"{_prov_substitute_internal_rel('phi', 't', 'v', 'phi_r')}"
)

_SUBST_GRAPH_NOT_RECONSTRUCT = (
    f"!phi t v phi_r. "
    f"{_prov_substitute_internal_rel('phi', 't', 'v', 'phi_r')} ==> "
    f"{_prov_substitute_internal_rel('Not_f phi', 't', 'v', 'Not_f phi_r')}"
)

_SUBST_GRAPH_INSERT_RECONSTRUCT = (
    f"!a b t v ar br. "
    f"{_prov_substitute_internal_rel('a', 't', 'v', 'ar')} ==> "
    f"{_prov_substitute_internal_rel('b', 't', 'v', 'br')} ==> "
    f"{_prov_substitute_internal_rel('Insert_t a b', 't', 'v', 'Insert_t ar br')}"
)

_SUBST_GRAPH_EQ_RECONSTRUCT = (
    f"!a b t v ar br. "
    f"{_prov_substitute_internal_rel('a', 't', 'v', 'ar')} ==> "
    f"{_prov_substitute_internal_rel('b', 't', 'v', 'br')} ==> "
    f"{_prov_substitute_internal_rel('Eq_f a b', 't', 'v', 'Eq_f ar br')}"
)

_SUBST_GRAPH_IN_RECONSTRUCT = (
    f"!a b t v ar br. "
    f"{_prov_substitute_internal_rel('a', 't', 'v', 'ar')} ==> "
    f"{_prov_substitute_internal_rel('b', 't', 'v', 'br')} ==> "
    f"{_prov_substitute_internal_rel('In_a a b', 't', 'v', 'In_a ar br')}"
)

_SUBST_GRAPH_IMP_RECONSTRUCT = (
    f"!p q t v pr qr. "
    f"{_prov_substitute_internal_rel('p', 't', 'v', 'pr')} ==> "
    f"{_prov_substitute_internal_rel('q', 't', 'v', 'qr')} ==> "
    f"{_prov_substitute_internal_rel('Imp_f p q', 't', 'v', 'Imp_f pr qr')}"
)

_SUBST_GRAPH_FORALL_HIT_RECONSTRUCT = (
    f"!w body t v. w = v ==> "
    f"{_prov_substitute_internal_rel('Forall_f w body', 't', 'v', 'Forall_f w body')}"
)

_SUBST_GRAPH_FORALL_MISS_RECONSTRUCT = (
    f"!w body t v body_r. ~(w = v) ==> "
    f"{_prov_substitute_internal_rel('body', 't', 'v', 'body_r')} ==> "
    f"{_prov_substitute_internal_rel('Forall_f w body', 't', 'v', 'Forall_f w body_r')}"
)


@proof
def SUBSTITUTE_GRAPH_NOT_ELIMINATES(p):
    """Object-level graph witness elimination for a ``Not_f`` entry."""
    p.goal(_SUBST_GRAPH_NOT_ELIM)
    # DSL/proof friction: this should unfold ``substitute_internal``,
    # eliminate the parent trace-set witness, select the Not_f branch from
    # the validity proof for the parent entry, then reuse the same trace set
    # as the child relation witness.  The DSL has no packaged helper for
    # "open an internal Sigma_1 graph certificate and project one trace
    # edge" yet.
    p.sorry()


@proof
def SUBSTITUTE_GRAPH_NOT_RECONSTRUCTS(p):
    """Object-level graph witness reconstruction for a ``Not_f`` entry."""
    p.goal(_SUBST_GRAPH_NOT_RECONSTRUCT)
    # DSL/proof friction: this should extend the child trace-set witness
    # with ``Pair_ord (Not_f phi) (Not_f phi_r)`` and prove the new
    # universal validity clause by splitting on the fresh edge.  This is
    # the reusable graph-extension lemma that the remaining unary/binary
    # constructor rules should share.
    p.sorry()


@proof
def SUBSTITUTE_GRAPH_INSERT_RECONSTRUCTS(p):
    """Object-level graph witness reconstruction for an ``Insert_t`` entry."""
    p.goal(_SUBST_GRAPH_INSERT_RECONSTRUCT)
    # DSL/proof friction: should merge/extend two child trace-set witnesses
    # with the parent ``Pair_ord (Insert_t a b) (Insert_t ar br)`` edge,
    # then prove the universal validity clause by splitting on the fresh
    # edge and delegating old edges back to the two child certificates.
    p.sorry()


@proof
def SUBSTITUTE_GRAPH_EQ_RECONSTRUCTS(p):
    """Object-level graph witness reconstruction for an ``Eq_f`` entry."""
    p.goal(_SUBST_GRAPH_EQ_RECONSTRUCT)
    # DSL/proof friction: same binary graph-extension pattern as Insert_t,
    # but selecting the Eq_f branch of ``_support_subst_step_body``.
    p.sorry()


@proof
def SUBSTITUTE_GRAPH_IN_RECONSTRUCTS(p):
    """Object-level graph witness reconstruction for an ``In_a`` entry."""
    p.goal(_SUBST_GRAPH_IN_RECONSTRUCT)
    # DSL/proof friction: same binary graph-extension pattern as Insert_t,
    # selecting the In_a branch of ``_support_subst_step_body``.
    p.sorry()


@proof
def SUBSTITUTE_GRAPH_IMP_RECONSTRUCTS(p):
    """Object-level graph witness reconstruction for an ``Imp_f`` entry."""
    p.goal(_SUBST_GRAPH_IMP_RECONSTRUCT)
    # DSL/proof friction: same binary graph-extension pattern as Insert_t,
    # selecting the Imp_f branch of ``_support_subst_step_body``.
    p.sorry()


@proof
def SUBSTITUTE_GRAPH_FORALL_HIT_RECONSTRUCTS(p):
    """Object-level graph witness reconstruction for a shadowed binder."""
    p.goal(_SUBST_GRAPH_FORALL_HIT_RECONSTRUCT)
    # DSL/proof friction: should construct a one-edge extension witnessing
    # the Forall_f hit branch, where the output is the unchanged parent.
    p.sorry()


@proof
def SUBSTITUTE_GRAPH_FORALL_MISS_RECONSTRUCTS(p):
    """Object-level graph witness reconstruction for a non-shadowed binder."""
    p.goal(_SUBST_GRAPH_FORALL_MISS_RECONSTRUCT)
    # DSL/proof friction: should extend the body child certificate with the
    # parent Forall_f edge and select the miss branch using ``~(w = v)``.
    p.sorry()


@proof
def SUBSTITUTE_REC_EMPTY(p):
    """Base case for the internal substitute graph."""
    p.goal(_SUBST_RULE_EMPTY)
    p.fix("t v")
    p.have("hsyntax: is_term Empty_t \\/ is_form Empty_t").by_thm(
        DISJ1(IS_TERM_EMPTY, p._parse("is_form Empty_t"))
    )
    equiv = SPECL(
        [
            p._parse("Empty_t"),
            p._parse("t"),
            p._parse("v"),
            p._parse("Empty_t"),
        ],
        SUBSTITUTE_INTERNAL_EQUIV,
    )
    p.have(
        "h_rel_eq: "
        f"{_prov_substitute_internal_rel('Empty_t', 't', 'v', 'Empty_t')} "
        "= (Empty_t = ((substitute Empty_t) t) v)"
    ).by(equiv, "hsyntax")
    p.have("h_rhs: Empty_t = ((substitute Empty_t) t) v").by_rewrite(
        [SUBSTITUTE_AT_EMPTY]
    )
    # DSL friction: the direct proof should construct the graph witness
    # inside ``substitute_internal``.  The compact available route uses the
    # exported graph equivalence, so this proof belongs above core.
    p.thus(_prov_substitute_internal_rel("Empty_t", "t", "v", "Empty_t")).by_eq_mp(
        "h_rel_eq", "h_rhs"
    )


@proof
def SUBSTITUTE_REC_VAR_HIT(p):
    """Variable-hit case for the internal substitute graph."""
    p.goal(_SUBST_RULE_VAR_HIT)
    p.fix("x t v")
    p.assume("hxv: x = v")
    p.have("h_var_term: is_term (Var_t x)").by_thm(
        EQT_ELIM(SPEC(p._parse("x"), IS_TERM_AT_VAR))
    )
    p.have("hsyntax: is_term (Var_t x) \\/ is_form (Var_t x)").by_thm(
        DISJ1(p.fact("h_var_term"), p._parse("is_form (Var_t x)"))
    )
    equiv = SPECL(
        [
            p._parse("Var_t x"),
            p._parse("t"),
            p._parse("v"),
            p._parse("t"),
        ],
        SUBSTITUTE_INTERNAL_EQUIV,
    )
    p.have(
        "h_rel_eq: "
        f"{_prov_substitute_internal_rel('Var_t x', 't', 'v', 't')} "
        "= (t = ((substitute (Var_t x)) t) v)"
    ).by(equiv, "hsyntax")
    p.have("hvx: v = x").by_thm(SYM(p.fact("hxv")))
    p.have("h_subst: ((substitute (Var_t x)) t) v = t").by(
        SUBSTITUTE_AT_VAR_HIT, "x", "t", "v", "hvx"
    )
    p.have("h_rhs: t = ((substitute (Var_t x)) t) v").by_thm(SYM(p.fact("h_subst")))
    # DSL friction: ``SUBSTITUTE_AT_VAR_HIT`` is keyed by ``v = x`` while
    # the constructor package states ``x = v``.
    p.thus(_prov_substitute_internal_rel("Var_t x", "t", "v", "t")).by_eq_mp(
        "h_rel_eq", "h_rhs"
    )


@proof
def SUBSTITUTE_REC_VAR_MISS(p):
    """Variable-miss case for the internal substitute graph."""
    p.goal(_SUBST_RULE_VAR_MISS)
    p.fix("x t v")
    p.assume("hxne: ~(x = v)")
    p.have("h_var_term: is_term (Var_t x)").by_thm(
        EQT_ELIM(SPEC(p._parse("x"), IS_TERM_AT_VAR))
    )
    p.have("hsyntax: is_term (Var_t x) \\/ is_form (Var_t x)").by_thm(
        DISJ1(p.fact("h_var_term"), p._parse("is_form (Var_t x)"))
    )
    equiv = SPECL(
        [
            p._parse("Var_t x"),
            p._parse("t"),
            p._parse("v"),
            p._parse("Var_t x"),
        ],
        SUBSTITUTE_INTERNAL_EQUIV,
    )
    p.have(
        "h_rel_eq: "
        f"{_prov_substitute_internal_rel('Var_t x', 't', 'v', 'Var_t x')} "
        "= (Var_t x = ((substitute (Var_t x)) t) v)"
    ).by(equiv, "hsyntax")
    hvx = ASSUME(p._parse("v = x"))
    hxv = SYM(hvx)
    F_th = MP(NOT_ELIM(p.fact("hxne")), hxv)
    p.have("hvne: ~(v = x)").by_thm(NOT_INTRO(DISCH(p._parse("v = x"), F_th)))
    p.have("h_subst: ((substitute (Var_t x)) t) v = Var_t x").by(
        SUBSTITUTE_AT_VAR_MISS, "x", "t", "v", "hvne"
    )
    p.have("h_rhs: Var_t x = ((substitute (Var_t x)) t) v").by_thm(
        SYM(p.fact("h_subst"))
    )
    # DSL friction: deriving symmetric negated equality still needs an
    # explicit NOT_INTRO/DISCH block.
    p.thus(_prov_substitute_internal_rel("Var_t x", "t", "v", "Var_t x")).by_eq_mp(
        "h_rel_eq", "h_rhs"
    )


@proof
def SUBSTITUTE_REC_NOT(p):
    """Constructor step for ``Not_f`` in the internal substitute graph."""
    p.goal(_SUBST_RULE_NOT)
    p.fix("phi t v phi_r")
    p.assume("h_child: " + _prov_substitute_internal_rel("phi", "t", "v", "phi_r"))
    p.thus(
        _prov_substitute_internal_rel("Not_f phi", "t", "v", "Not_f phi_r")
    ).by(SUBSTITUTE_GRAPH_NOT_RECONSTRUCTS, "phi", "t", "v", "phi_r", "h_child")


@proof
def SUBSTITUTE_REC_INSERT(p):
    """Constructor step for ``Insert_t`` in the internal substitute graph."""
    p.goal(_SUBST_RULE_INSERT)
    p.fix("a b t v ar br")
    p.assume("ha: " + _prov_substitute_internal_rel("a", "t", "v", "ar"))
    p.assume("hb: " + _prov_substitute_internal_rel("b", "t", "v", "br"))
    p.thus(
        _prov_substitute_internal_rel("Insert_t a b", "t", "v", "Insert_t ar br")
    ).by(SUBSTITUTE_GRAPH_INSERT_RECONSTRUCTS, "a", "b", "t", "v", "ar", "br", "ha", "hb")


@proof
def SUBSTITUTE_REC_EQ(p):
    """Constructor step for ``Eq_f`` in the internal substitute graph."""
    p.goal(_SUBST_RULE_EQ)
    p.fix("a b t v ar br")
    p.assume("ha: " + _prov_substitute_internal_rel("a", "t", "v", "ar"))
    p.assume("hb: " + _prov_substitute_internal_rel("b", "t", "v", "br"))
    p.thus(
        _prov_substitute_internal_rel("Eq_f a b", "t", "v", "Eq_f ar br")
    ).by(SUBSTITUTE_GRAPH_EQ_RECONSTRUCTS, "a", "b", "t", "v", "ar", "br", "ha", "hb")


@proof
def SUBSTITUTE_REC_IN(p):
    """Constructor step for ``In_a`` in the internal substitute graph."""
    p.goal(_SUBST_RULE_IN)
    p.fix("a b t v ar br")
    p.assume("ha: " + _prov_substitute_internal_rel("a", "t", "v", "ar"))
    p.assume("hb: " + _prov_substitute_internal_rel("b", "t", "v", "br"))
    p.thus(
        _prov_substitute_internal_rel("In_a a b", "t", "v", "In_a ar br")
    ).by(SUBSTITUTE_GRAPH_IN_RECONSTRUCTS, "a", "b", "t", "v", "ar", "br", "ha", "hb")


@proof
def SUBSTITUTE_REC_IMP(p):
    """Constructor step for ``Imp_f`` in the internal substitute graph."""
    p.goal(_SUBST_RULE_IMP)
    p.fix("p q t v pr qr")
    p.assume("hp: " + _prov_substitute_internal_rel("p", "t", "v", "pr"))
    p.assume("hq: " + _prov_substitute_internal_rel("q", "t", "v", "qr"))
    p.thus(
        _prov_substitute_internal_rel("Imp_f p q", "t", "v", "Imp_f pr qr")
    ).by(SUBSTITUTE_GRAPH_IMP_RECONSTRUCTS, "p", "q", "t", "v", "pr", "qr", "hp", "hq")


@proof
def SUBSTITUTE_REC_FORALL_HIT(p):
    """Binder-hit case for ``Forall_f`` in the internal substitute graph."""
    p.goal(_SUBST_RULE_FORALL_HIT)
    p.fix("w body t v")
    p.assume("hwv: w = v")
    p.thus(
        _prov_substitute_internal_rel(
            "Forall_f w body", "t", "v", "Forall_f w body"
        )
    ).by(SUBSTITUTE_GRAPH_FORALL_HIT_RECONSTRUCTS, "w", "body", "t", "v", "hwv")


@proof
def SUBSTITUTE_REC_FORALL_MISS(p):
    """Binder-miss case for ``Forall_f`` in the internal substitute graph."""
    p.goal(_SUBST_RULE_FORALL_MISS)
    p.fix("w body t v body_r")
    p.assume("hwne: ~(w = v)")
    p.assume("hbody: " + _prov_substitute_internal_rel("body", "t", "v", "body_r"))
    p.thus(
        _prov_substitute_internal_rel(
            "Forall_f w body", "t", "v", "Forall_f w body_r"
        )
    ).by(
        SUBSTITUTE_GRAPH_FORALL_MISS_RECONSTRUCTS,
        "w", "body", "t", "v", "body_r", "hwne", "hbody",
    )


@proof
def HF_SYNTAX_REC_PACKAGE(p):
    r"""Syntax-recursion eliminator for internal substitute representation."""
    p.goal(
        f"({_SUBST_RULE_EMPTY}) ==> "
        f"({_SUBST_RULE_VAR_HIT}) ==> "
        f"({_SUBST_RULE_VAR_MISS}) ==> "
        f"({_SUBST_RULE_INSERT}) ==> "
        f"({_SUBST_RULE_EQ}) ==> "
        f"({_SUBST_RULE_IN}) ==> "
        f"({_SUBST_RULE_NOT}) ==> "
        f"({_SUBST_RULE_IMP}) ==> "
        f"({_SUBST_RULE_FORALL_HIT}) ==> "
        f"({_SUBST_RULE_FORALL_MISS}) ==> "
        f"({_SUBST_HEADLINE_SYNTACTIC})"
    )
    p.sorry()


def _derive_substitute_represents_syntactic():
    th = HF_SYNTAX_REC_PACKAGE
    for rule in [
        SUBSTITUTE_REC_EMPTY,
        SUBSTITUTE_REC_VAR_HIT,
        SUBSTITUTE_REC_VAR_MISS,
        SUBSTITUTE_REC_INSERT,
        SUBSTITUTE_REC_EQ,
        SUBSTITUTE_REC_IN,
        SUBSTITUTE_REC_NOT,
        SUBSTITUTE_REC_IMP,
        SUBSTITUTE_REC_FORALL_HIT,
        SUBSTITUTE_REC_FORALL_MISS,
    ]:
        th = MP(th, rule)
    return th


SUBSTITUTE_REPRESENTS_SYNTACTIC = _derive_substitute_represents_syntactic()


@proof
def SUBSTITUTE_REPRESENTS_TERM(p):
    """|- !phi t v. is_term phi ==> Prov_HF(substitute_internal phi t v ...)."""
    p.goal(
        f"!phi t v. is_term phi ==> "
        f"{_prov_substitute_internal_rel('phi', 't', 'v', '((substitute phi) t) v')}"
    )
    p.fix("phi t v")
    p.assume("hphi: is_term phi")
    p.have("hsyntax: is_term phi \\/ is_form phi").by_thm(
        DISJ1(p.fact("hphi"), p._parse("is_form phi"))
    )
    p.thus(_prov_substitute_internal_rel("phi", "t", "v", "((substitute phi) t) v")).by(
        SUBSTITUTE_REPRESENTS_SYNTACTIC, "phi", "t", "v", "hsyntax"
    )


@proof
def SUBSTITUTE_REPRESENTS_FORM(p):
    """|- !phi t v. is_form phi ==> Prov_HF(substitute_internal phi t v ...)."""
    p.goal(
        f"!phi t v. is_form phi ==> "
        f"{_prov_substitute_internal_rel('phi', 't', 'v', '((substitute phi) t) v')}"
    )
    p.fix("phi t v")
    p.assume("hphi: is_form phi")
    p.have("hsyntax: is_term phi \\/ is_form phi").by_thm(
        DISJ2(p._parse("is_term phi"), p.fact("hphi"))
    )
    p.thus(_prov_substitute_internal_rel("phi", "t", "v", "((substitute phi) t) v")).by(
        SUBSTITUTE_REPRESENTS_SYNTACTIC, "phi", "t", "v", "hsyntax"
    )


SUBSTITUTE_REPRESENTS = SUBSTITUTE_REPRESENTS_FORM


@proof
def TEMPLATE_FILL_REPRESENTS_TERM(p):
    """|- !D t v. is_term D ==> Prov_HF(template_fill_internal D t v ...)."""
    p.goal(
        f"!D t v. is_term D ==> "
        f"{_prov_template_fill_internal_rel('D', 't', 'v', 'template_fill D t v')}"
    )
    p.fix("D t v")
    p.assume("hD: is_term D")
    p.have(
        "h_subst: "
        f"{_prov_substitute_internal_rel('D', 't', 'v', '((substitute D) t) v')}"
    ).by(SUBSTITUTE_REPRESENTS_TERM, "D", "t", "v", "hD")
    p.have("h_eq: template_fill D t v = substitute D t v").by(
        TEMPLATE_FILL_EQ_SUBSTITUTE_TERM, "D", "t", "v", "hD",
    )
    p.thus(
        _prov_template_fill_internal_rel("D", "t", "v", "template_fill D t v")
    ).by_rewrite_of(
        "h_subst",
        [SYM(TEMPLATE_FILL_INTERNAL_DEF), SYM(p.fact("h_eq"))],
    )


TEMPLATE_FILL_REPRESENTS = TEMPLATE_FILL_REPRESENTS_TERM

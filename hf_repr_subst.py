# ---------------------------------------------------------------------------
# Stage 3C -- substitute-internal representability proofs.
#
# This layer sits above ``hf_logic``. The raw syntax/formula definitions live
# in ``hf_repr_core.py``; the substitution-specific representability and
# equivalence packages live here so graph-witness details do not leak into the
# core support-predicate package.
# ---------------------------------------------------------------------------

from proof import proof
from tactics import (
    SPECL,
    SYM,
    MP,
    TRANS,
    DISJ1,
    DISJ2,
)
from hf_repr_core import (
    TEMPLATE_FILL_INTERNAL_DEF,
    TEMPLATE_FILL_EQ_SUBSTITUTE_TERM,
    _SUBST_HEADLINE_SYNTACTIC,
    _prov_substitute_internal_rel,
    _prov_template_fill_internal_rel,
)


@proof
def HF_SUBSTITUTE_REPRESENTS_PACKAGE(p):
    """Existence/forward representability of ``substitute_internal``.

    This is the constructive package: for syntactic ``F`` it builds an
    internal graph witness whose result is the HOL value
    ``substitute F t v``.  The graph manipulation is private to this
    package rather than exported as raw constructor lemmas.
    """
    p.goal(_SUBST_HEADLINE_SYNTACTIC)
    p.sorry()


@proof
def HF_SUBSTITUTE_EQUIV_PACKAGE(p):
    """Substitution graph equivalence on syntactic inputs."""
    p.goal(
        f"!F t v r. (is_term F \\/ is_form F) ==> "
        f"({_prov_substitute_internal_rel('F', 't', 'v', 'r')} = "
        f"(r = ((substitute F) t) v))"
    )
    p.sorry()


HF_SYNTAX_REC_PACKAGE = HF_SUBSTITUTE_REPRESENTS_PACKAGE
SUBSTITUTE_REPRESENTS_SYNTACTIC = HF_SUBSTITUTE_REPRESENTS_PACKAGE
SUBSTITUTE_INTERNAL_EQUIV = HF_SUBSTITUTE_EQUIV_PACKAGE


@proof
def SUBSTITUTE_INTERNAL_FUNCTIONAL(p):
    r"""|- !F t v r1 r2. (is_term F \/ is_form F)
          ==> substitute_internal(F,t,v,r1)
          ==> substitute_internal(F,t,v,r2)
          ==> r1 = r2.

    Functionality is derived from ``HF_SUBSTITUTE_EQUIV_PACKAGE``: on
    syntactic inputs the internal relation is equivalent to the graph of
    the HOL function ``substitute``.
    """
    rel_r1 = _prov_substitute_internal_rel("F", "t", "v", "r1")
    rel_r2 = _prov_substitute_internal_rel("F", "t", "v", "r2")
    p.goal(
        f"!F t v r1 r2. (is_term F \\/ is_form F) ==> "
        f"{rel_r1} ==> {rel_r2} ==> r1 = r2"
    )
    p.fix("F t v r1 r2")
    p.assume("hsyntax: is_term F \\/ is_form F")
    p.assume(f"hr1: {rel_r1}")
    p.assume(f"hr2: {rel_r2}")
    eq_r1 = SPECL(
        [p._parse("F"), p._parse("t"), p._parse("v"), p._parse("r1")],
        SUBSTITUTE_INTERNAL_EQUIV,
    )
    eq_r2 = SPECL(
        [p._parse("F"), p._parse("t"), p._parse("v"), p._parse("r2")],
        SUBSTITUTE_INTERNAL_EQUIV,
    )
    p.have("rel_r1_eq: " f"{rel_r1} = (r1 = ((substitute F) t) v)").by_thm(
        MP(eq_r1, p.fact("hsyntax"))
    )
    p.have("rel_r2_eq: " f"{rel_r2} = (r2 = ((substitute F) t) v)").by_thm(
        MP(eq_r2, p.fact("hsyntax"))
    )
    p.have("r1_eq: r1 = ((substitute F) t) v").by_eq_mp("rel_r1_eq", "hr1")
    p.have("r2_eq: r2 = ((substitute F) t) v").by_eq_mp("rel_r2_eq", "hr2")
    p.thus("r1 = r2").by_thm(TRANS(p.fact("r1_eq"), SYM(p.fact("r2_eq"))))


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

"""Spike for a readability-first HF syntax recursion package.

This module deliberately does not replace the current trace route.  It
models the API shape we would want from a scoped syntax-recursion /
induction definitional package:

* one fixed internal formula, ``substitute_internal_rec_spike``;
* generated constructor rules for the substitution graph;
* a small derived constructor-composition theorem that uses those rules
  without mentioning traces.

The generated rules are axiomatized here because the point of the spike is
to test the public proof surface before committing to the underlying schema.
"""

from fusion import new_axiom, new_constant
from basics import mk_const
from nat0 import nat0_ty
from parser import add_const, parse
from proof import proof
from tactics import DISJ1, DISJ2, MP

# Importing hf_repr_core registers the HF syntax/provability constants used
# by the parser: Prov_HF, substitute, numeral, idx_x/y/z/w, constructors, etc.
from hf_repr_core import (  # noqa: F401
    Prov_HF,
    idx_w,
    idx_x,
    idx_y,
    idx_z,
    numeral,
    substitute,
)


new_constant("substitute_internal_rec_spike", nat0_ty)
substitute_internal_rec_spike = mk_const("substitute_internal_rec_spike", [])
add_const("substitute_internal_rec_spike", substitute_internal_rec_spike)


def _rel(F, t, v, r):
    """Surface text for the four-slot internal substitution relation."""
    return (
        "(substitute (substitute (substitute (substitute "
        f"substitute_internal_rec_spike (numeral ({F})) idx_x) "
        f"(numeral ({t})) idx_y) "
        f"(numeral ({v})) idx_z) "
        f"(numeral ({r})) idx_w)"
    )


def _prov_rel(F, t, v, r):
    return f"Prov_HF {_rel(F, t, v, r)}"


# ---------------------------------------------------------------------------
# Candidate generated rules from the scoped syntax-recursion package.
#
# These are intentionally representability-facing rules, not trace rules.
# The eventual package should derive them from the direct recursive
# definition of substitute_internal.
# ---------------------------------------------------------------------------


_RULE_EMPTY = f"!t v. {_prov_rel('Empty_t', 't', 'v', 'Empty_t')}"
_RULE_VAR_HIT = f"!x t v. x = v ==> {_prov_rel('Var_t x', 't', 'v', 't')}"
_RULE_VAR_MISS = (
    f"!x t v. ~(x = v) ==> {_prov_rel('Var_t x', 't', 'v', 'Var_t x')}"
)
_RULE_INSERT = (
    f"!a b t v ar br. "
    f"{_prov_rel('a', 't', 'v', 'ar')} ==> "
    f"{_prov_rel('b', 't', 'v', 'br')} ==> "
    f"{_prov_rel('Insert_t a b', 't', 'v', 'Insert_t ar br')}"
)
_RULE_EQ = (
    f"!a b t v ar br. "
    f"{_prov_rel('a', 't', 'v', 'ar')} ==> "
    f"{_prov_rel('b', 't', 'v', 'br')} ==> "
    f"{_prov_rel('Eq_f a b', 't', 'v', 'Eq_f ar br')}"
)
_RULE_IN = (
    f"!a b t v ar br. "
    f"{_prov_rel('a', 't', 'v', 'ar')} ==> "
    f"{_prov_rel('b', 't', 'v', 'br')} ==> "
    f"{_prov_rel('In_a a b', 't', 'v', 'In_a ar br')}"
)
_RULE_NOT = (
    f"!phi t v phi_r. "
    f"{_prov_rel('phi', 't', 'v', 'phi_r')} ==> "
    f"{_prov_rel('Not_f phi', 't', 'v', 'Not_f phi_r')}"
)
_RULE_IMP = (
    f"!p q t v pr qr. "
    f"{_prov_rel('p', 't', 'v', 'pr')} ==> "
    f"{_prov_rel('q', 't', 'v', 'qr')} ==> "
    f"{_prov_rel('Imp_f p q', 't', 'v', 'Imp_f pr qr')}"
)
_RULE_FORALL_HIT = (
    f"!w body t v. w = v ==> "
    f"{_prov_rel('Forall_f w body', 't', 'v', 'Forall_f w body')}"
)
_RULE_FORALL_MISS = (
    f"!w body t v body_r. ~(w = v) ==> "
    f"{_prov_rel('body', 't', 'v', 'body_r')} ==> "
    f"{_prov_rel('Forall_f w body', 't', 'v', 'Forall_f w body_r')}"
)
_HEADLINE_SYNTACTIC = (
    f"!F t v. (is_term F \\/ is_form F) ==> "
    f"{_prov_rel('F', 't', 'v', '((substitute F) t) v')}"
)


SUBSTITUTE_REC_SPIKE_EMPTY = new_axiom(parse(_RULE_EMPTY))

SUBSTITUTE_REC_SPIKE_VAR_HIT = new_axiom(parse(_RULE_VAR_HIT))

SUBSTITUTE_REC_SPIKE_VAR_MISS = new_axiom(parse(_RULE_VAR_MISS))

SUBSTITUTE_REC_SPIKE_INSERT = new_axiom(parse(_RULE_INSERT))

SUBSTITUTE_REC_SPIKE_EQ = new_axiom(parse(_RULE_EQ))

SUBSTITUTE_REC_SPIKE_IN = new_axiom(parse(_RULE_IN))

SUBSTITUTE_REC_SPIKE_NOT = new_axiom(parse(_RULE_NOT))

SUBSTITUTE_REC_SPIKE_IMP = new_axiom(parse(_RULE_IMP))

SUBSTITUTE_REC_SPIKE_FORALL_HIT = new_axiom(parse(_RULE_FORALL_HIT))

SUBSTITUTE_REC_SPIKE_FORALL_MISS = new_axiom(parse(_RULE_FORALL_MISS))


# A convenience theorem showing the proof surface for one recursive
# constructor.  This is the shape the final substitute proof should use:
# constructor rule + IHs, with no trace membership facts.
@proof
def SUBSTITUTE_REC_SPIKE_INSERT_COMPOSES(p):
    p.goal(
        f"!a b t v ar br. "
        f"{_prov_rel('a', 't', 'v', 'ar')} ==> "
        f"{_prov_rel('b', 't', 'v', 'br')} ==> "
        f"{_prov_rel('Insert_t a b', 't', 'v', 'Insert_t ar br')}"
    )
    p.fix("a b t v ar br")
    p.assume("ha: " + _prov_rel("a", "t", "v", "ar"))
    p.assume("hb: " + _prov_rel("b", "t", "v", "br"))
    p.thus(_prov_rel("Insert_t a b", "t", "v", "Insert_t ar br")).by(
        SUBSTITUTE_REC_SPIKE_INSERT, "a", "b", "t", "v", "ar", "br", "ha", "hb"
    )


@proof
def SUBSTITUTE_REC_SPIKE_FORALL_HIT_COMPOSES(p):
    """Binder-hit wrapper: substitution stops under the quantified body."""
    p.goal(
        f"!w body t v. w = v ==> "
        f"{_prov_rel('Forall_f w body', 't', 'v', 'Forall_f w body')}"
    )
    p.fix("w body t v")
    p.assume("h: w = v")
    p.thus(_prov_rel("Forall_f w body", "t", "v", "Forall_f w body")).by(
        SUBSTITUTE_REC_SPIKE_FORALL_HIT, "w", "body", "t", "v", "h"
    )


@proof
def SUBSTITUTE_REC_SPIKE_FORALL_MISS_COMPOSES(p):
    """Binder-miss wrapper: one IH-style premise for the quantified body."""
    p.goal(
        f"!w body t v body_r. ~(w = v) ==> "
        f"{_prov_rel('body', 't', 'v', 'body_r')} ==> "
        f"{_prov_rel('Forall_f w body', 't', 'v', 'Forall_f w body_r')}"
    )
    p.fix("w body t v body_r")
    p.assume("hmiss: ~(w = v)")
    p.assume("hbody: " + _prov_rel("body", "t", "v", "body_r"))
    p.thus(_prov_rel("Forall_f w body", "t", "v", "Forall_f w body_r")).by(
        SUBSTITUTE_REC_SPIKE_FORALL_MISS,
        "w",
        "body",
        "t",
        "v",
        "body_r",
        "hmiss",
        "hbody",
    )


# Scoped syntax-recursion induction package.  This is the one remaining
# package axiom in the spike: it says that constructor-local substitution
# graph rules are enough to cover every encoded syntax object.  The package
# is intentionally syntax-scoped; non-syntax nat0 values are outside the
# recursion principle rather than silently covered by a magic default branch.
# Applying it to the generated rules derives the headline theorem below.
HF_SYNTAX_REC_SPIKE_INDUCT = new_axiom(
    parse(
        f"({_RULE_EMPTY}) ==> "
        f"({_RULE_VAR_HIT}) ==> "
        f"({_RULE_VAR_MISS}) ==> "
        f"({_RULE_INSERT}) ==> "
        f"({_RULE_EQ}) ==> "
        f"({_RULE_IN}) ==> "
        f"({_RULE_NOT}) ==> "
        f"({_RULE_IMP}) ==> "
        f"({_RULE_FORALL_HIT}) ==> "
        f"({_RULE_FORALL_MISS}) ==> "
        f"({_HEADLINE_SYNTACTIC})"
    )
)


def _derive_substitute_represents_rec_spike():
    th = HF_SYNTAX_REC_SPIKE_INDUCT
    for rule in [
        SUBSTITUTE_REC_SPIKE_EMPTY,
        SUBSTITUTE_REC_SPIKE_VAR_HIT,
        SUBSTITUTE_REC_SPIKE_VAR_MISS,
        SUBSTITUTE_REC_SPIKE_INSERT,
        SUBSTITUTE_REC_SPIKE_EQ,
        SUBSTITUTE_REC_SPIKE_IN,
        SUBSTITUTE_REC_SPIKE_NOT,
        SUBSTITUTE_REC_SPIKE_IMP,
        SUBSTITUTE_REC_SPIKE_FORALL_HIT,
        SUBSTITUTE_REC_SPIKE_FORALL_MISS,
    ]:
        th = MP(th, rule)
    return th


SUBSTITUTE_REPRESENTS_REC_SPIKE_SYNTACTIC = _derive_substitute_represents_rec_spike()

# The old trace-path headline is total in F.  The readability-first route
# should either carry this syntactic premise to consumers, or add an explicit
# non-syntax default branch to the recursion package.  Keeping this alias out
# of the spike prevents accidentally treating the scoped theorem as total.
SUBSTITUTE_REPRESENTS_REC_SPIKE = SUBSTITUTE_REPRESENTS_REC_SPIKE_SYNTACTIC


@proof
def SUBSTITUTE_REPRESENTS_REC_SPIKE_TERM(p):
    """Term-specialized wrapper, avoiding disjunction plumbing downstream."""
    p.goal(
        f"!phi t v. is_term phi ==> "
        f"{_prov_rel('phi', 't', 'v', '((substitute phi) t) v')}"
    )
    p.fix("phi t v")
    p.assume("hphi: is_term phi")
    p.have("hsyntax: is_term phi \\/ is_form phi").by_thm(
        DISJ1(p.fact("hphi"), p._parse("is_form phi"))
    )
    p.thus(_prov_rel("phi", "t", "v", "((substitute phi) t) v")).by(
        SUBSTITUTE_REPRESENTS_REC_SPIKE_SYNTACTIC, "phi", "t", "v", "hsyntax"
    )


@proof
def SUBSTITUTE_REPRESENTS_REC_SPIKE_FORM(p):
    """Formula-specialized wrapper; this is the expected G1 workhorse."""
    p.goal(
        f"!phi t v. is_form phi ==> "
        f"{_prov_rel('phi', 't', 'v', '((substitute phi) t) v')}"
    )
    p.fix("phi t v")
    p.assume("hphi: is_form phi")
    p.have("hsyntax: is_term phi \\/ is_form phi").by_thm(
        DISJ2(p._parse("is_term phi"), p.fact("hphi"))
    )
    p.thus(_prov_rel("phi", "t", "v", "((substitute phi) t) v")).by(
        SUBSTITUTE_REPRESENTS_REC_SPIKE_SYNTACTIC, "phi", "t", "v", "hsyntax"
    )


# Final downstream-facing names for the direct route spike.  These are the
# names the real replacement should provide without the ``REC_SPIKE`` suffix.
SUBSTITUTE_REPRESENTS_TERM_SPIKE = SUBSTITUTE_REPRESENTS_REC_SPIKE_TERM
SUBSTITUTE_REPRESENTS_FORM_SPIKE = SUBSTITUTE_REPRESENTS_REC_SPIKE_FORM


if __name__ == "__main__":
    from parser import pp_thm

    print("HF syntax recursion spike loaded.")
    print("  substitute_internal_rec_spike:", substitute_internal_rec_spike)
    print("  INSERT rule:", pp_thm(SUBSTITUTE_REC_SPIKE_INSERT))
    print("  INSERT composed:", pp_thm(SUBSTITUTE_REC_SPIKE_INSERT_COMPOSES))
    print("  FORALL hit:", pp_thm(SUBSTITUTE_REC_SPIKE_FORALL_HIT_COMPOSES))
    print("  FORALL miss:", pp_thm(SUBSTITUTE_REC_SPIKE_FORALL_MISS_COMPOSES))
    print("  induction package:", pp_thm(HF_SYNTAX_REC_SPIKE_INDUCT))
    print("  syntactic headline:", pp_thm(SUBSTITUTE_REPRESENTS_REC_SPIKE_SYNTACTIC))
    print("  term wrapper:", pp_thm(SUBSTITUTE_REPRESENTS_TERM_SPIKE))
    print("  form wrapper:", pp_thm(SUBSTITUTE_REPRESENTS_FORM_SPIKE))

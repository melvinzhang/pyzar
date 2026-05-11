# ---------------------------------------------------------------------------
# Stage 2A (PRST) -- the PR-function-symbol mechanism.
# ---------------------------------------------------------------------------
#
# Every primitive recursive function in PRST gets:
#
#   (i)   a closed nat0 ``f_sym`` -- its function-symbol id;
#   (ii)  a declared arity ``pr_arity f_sym : nat0``;
#   (iii) one or more *defining equation* axioms, each of shape
#             |- Prov_PRST (Eq_pf (App_pt f_sym args)
#                                 <body in terms of args and previously
#                                  introduced symbols>).
#
# We bootstrap a small *base layer* of PR symbols by hand, then provide
# a *general PR introduction* mechanism that, given symbols for the
# inputs and a recursion scheme, produces a fresh ``f_sym`` plus its
# defining equations.
#
# The base layer follows the recursion-theoretic basis for PR set
# functions (Jensen-Karp 1971; Boolos-Burgess-Jeffrey ch. 6):
#
#   * Zero      : 0-ary, value Empty_pt.
#   * Proj_i_n  : n-ary, value (i+1)-th argument.
#   * Adj       : 2-ary, primitive. ``App_pt adj_sym (Tup_pt a (Tup_pt
#                 b Empty_pt))`` IS the adjunction operation -- there is
#                 no further-reducing defining equation, just as
#                 Empty_pt has no defining body. Adj is the only
#                 non-empty set constructor; it is a primitive PR
#                 symbol rather than a separate term constructor.
#   * If_in     : 4-ary case-split, dispatching on In_pa arg_1 arg_2:
#                     If_in a b x y := if In a b then x else y.
#   * Rec       : (n+2)-ary primitive recursion on the second argument's
#                 Adj-decomposition:
#                     Rec g h Empty_pt          y_vec = g(y_vec)
#                     Rec g h (Adj_pt i s)      y_vec
#                         = h(i, s, Rec g h s y_vec, y_vec)
#                                                  if ~In_pa i s
#                     Rec g h (Adj_pt i s)      y_vec
#                         = Rec g h s y_vec      otherwise.
#                 The side condition is the membership-canonical
#                 normalisation enforced by the bit-encoded carrier
#                 (cf. low_bit / clear_low in nat0).
#
# Substitution, numeral, diag, Proof_PRST -- all of them are definable in
# this base layer. Sketches for the four headline definitions appear at
# the bottom of this file.
#
# Stubs: every theorem here is sorried. The work is *cataloguing the
# axioms*, not proving any one of them; the discharges are uniform
# (each PR symbol's defining equation is justified by the kernel
# definition of its HOL counterpart plus a soundness lemma in
# ``godel_first_prst``).
# ---------------------------------------------------------------------------


from fusion import Var
from basics import mk_const, mk_app, mk_abs
from parser import define, parse_type
from nat0 import nat0_ty, define_unary_0
from nat0_order import define_wf_lt
from proof import proof, define_with_at
from tactics import SYM
from hf_syntax import (
    Var_t,
)
from prst_syntax import (
    Empty_pt,  # noqa: F401  -- parser alias in PR-defining-equation bodies; also nil-tuple
    Var_pt,  # noqa: F401  -- parser alias
    Eq_pf,  # noqa: F401  -- parser alias
    Not_pf,  # noqa: F401  -- parser alias
    Imp_pf,  # noqa: F401  -- parser alias
    In_pa,  # noqa: F401  -- parser alias
    App_pt,
    Tup_pt,  # noqa: F401  -- parser alias for args-tuple cons cells
    is_pterm,  # noqa: F401  -- parser alias
)


# ---------------------------------------------------------------------------
# Stage 2A (a) -- the function-symbol registry.
#
#   * ``is_pr_sym f`` :  ``f`` is a registered PR-function symbol id.
#   * ``pr_arity  f`` :  the declared arity of ``f`` (nat0).
#
# Both are HOL predicates / functions on nat0. They are *defined* (not
# axiomatized) so that the introduction of new PR symbols is a kernel
# extension, not a fresh axiom. In practice each new symbol bumps a
# fresh value of ``is_pr_sym`` via constructor disjointness.
# ---------------------------------------------------------------------------


# is_pr_sym / pr_arity are stub-defined in prst_syntax (forward ref
# from IS_PTERM_AT_APP). We re-import the constants here.
from prst_syntax import is_pr_sym, pr_arity  # noqa: F401, E402


# ---------------------------------------------------------------------------
# Stage 2A (b) -- the base layer of PR symbols.
#
# Each symbol is a fresh closed nat0 id. The choice of id is irrelevant
# for downstream reasoning; ``IS_PR_SYM_*`` and ``PR_ARITY_*`` pin the
# registry entry.
# ---------------------------------------------------------------------------


ZERO_SYM_DEF = define("zero_sym", parse_type("nat0"), "0")
zero_sym = mk_const("zero_sym", [])

ADJ_SYM_DEF = define("adj_sym", parse_type("nat0"), "SUC0 0")
adj_sym = mk_const("adj_sym", [])

PROJ_SYM_DEF = define(
    "proj_sym",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\i:nat0. \\n:nat0. Pair_ord (SUC0 (SUC0 0)) (Pair_ord i n)",
)
proj_sym = mk_const("proj_sym", [])

IF_IN_SYM_DEF = define("if_in_sym", parse_type("nat0"), "SUC0 (SUC0 (SUC0 0))")
if_in_sym = mk_const("if_in_sym", [])

REC_SYM_DEF = define(
    "rec_sym",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\g:nat0. \\h:nat0. Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 0)))) (Pair_ord g h)",
)
rec_sym = mk_const("rec_sym", [])


# ---------------------------------------------------------------------------
# Stage 2A (c) -- the base layer is registered.
# ---------------------------------------------------------------------------


# All five IS_PR_SYM_* lemmas follow the same shape: prove the
# disjunction that is the body of IS_PR_SYM_DEF applied to the symbol,
# then bridge through IS_PR_SYM_DEF via `by_unfold`. The literal-tag
# cases (zero / adj / if_in) discharge their disjunct by REFL after
# unfolding the symbol DEF; the existential cases (proj / rec) supply
# a witness via `disj_witness`.
#
# DSL friction: there is no "unfold-and-prove-a-disjunct" idiom in the
# DSL. Each lemma writes out the full 5-disjunct body explicitly. A
# `by_unfold_disj(IS_PR_SYM_DEF, witness=...)` helper would collapse
# the 6-line ritual to one call.
from prst_syntax import IS_PR_SYM_DEF  # noqa: E402

_IS_PR_SYM_BODY = (
    "{sym} = 0 \\/ "
    "{sym} = SUC0 0 \\/ "
    "(?i n. {sym} = Pair_ord (SUC0 (SUC0 0)) (Pair_ord i n)) \\/ "
    "{sym} = SUC0 (SUC0 (SUC0 0)) \\/ "
    "(?g h. {sym} = Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 0)))) (Pair_ord g h))"
)


@proof
def IS_PR_SYM_ZERO(p):
    """|- is_pr_sym zero_sym."""
    p.goal("is_pr_sym zero_sym")
    p.have("zero_eq: zero_sym = 0").by_thm(ZERO_SYM_DEF)
    p.have("h_body: " + _IS_PR_SYM_BODY.format(sym="zero_sym")).by_disj(
        "zero_eq"
    )
    p.thus("is_pr_sym zero_sym").by_unfold("h_body", IS_PR_SYM_DEF)


@proof
def IS_PR_SYM_ADJ(p):
    """|- is_pr_sym adj_sym."""
    p.goal("is_pr_sym adj_sym")
    p.have("adj_eq: adj_sym = SUC0 0").by_thm(ADJ_SYM_DEF)
    p.have("h_body: " + _IS_PR_SYM_BODY.format(sym="adj_sym")).by_disj("adj_eq")
    p.thus("is_pr_sym adj_sym").by_unfold("h_body", IS_PR_SYM_DEF)


@proof
def IS_PR_SYM_PROJ(p):
    """|- !i n. nat0_lt i n ==> is_pr_sym (proj_sym i n).

    The ``nat0_lt i n`` hypothesis is kept in the lemma's signature
    (Layer 5 PR-def axioms expect it as a side condition on proj
    arity-checks) but is not consumed here: ``is_pr_sym``'s body uses a
    bare existential ``?i n. ...`` without the guard, so the lemma is
    in fact unconditional on (i, n). The hypothesis falls out as
    vacuous after assumption.
    """
    p.goal(
        "!i n. nat0_lt i n ==> is_pr_sym (proj_sym i n)",
        types={"i": nat0_ty, "n": nat0_ty},
    )
    p.fix("i n")
    p.assume("_h_lt: nat0_lt i n")
    # `p.unfold` returns the beta-reduced specialization of PROJ_SYM_DEF.
    proj_eq_th = p.unfold(PROJ_SYM_DEF, "i", "n")
    p.have(
        "proj_eq: proj_sym i n = Pair_ord (SUC0 (SUC0 0)) (Pair_ord i n)"
    ).by_thm(proj_eq_th)
    # DSL friction: by_disj_witness is single-binder; the existential
    # leaf here is `?i n. ...` (two binders), so we prove the
    # existential first via by_exists and then DISJ it in.
    # Use fresh bound names `ii nn` to avoid shadowing the outer i, n
    # (otherwise by_unfold's alpha-match misses the unfolded `i' n'`).
    p.have(
        "h_ex: ?ii nn. proj_sym i n = Pair_ord (SUC0 (SUC0 0)) (Pair_ord ii nn)"
    ).by_exists(["i", "n"], "proj_eq")
    p.have(
        "h_body: " + _IS_PR_SYM_BODY.format(sym="proj_sym i n").replace(
            "?i n.", "?ii nn."
        ).replace("Pair_ord i n", "Pair_ord ii nn")
    ).by_disj("h_ex")
    p.thus("is_pr_sym (proj_sym i n)").by_unfold("h_body", IS_PR_SYM_DEF)


@proof
def IS_PR_SYM_IF_IN(p):
    """|- is_pr_sym if_in_sym."""
    p.goal("is_pr_sym if_in_sym")
    p.have("if_in_eq: if_in_sym = SUC0 (SUC0 (SUC0 0))").by_thm(IF_IN_SYM_DEF)
    p.have("h_body: " + _IS_PR_SYM_BODY.format(sym="if_in_sym")).by_disj(
        "if_in_eq"
    )
    p.thus("is_pr_sym if_in_sym").by_unfold("h_body", IS_PR_SYM_DEF)


@proof
def IS_PR_SYM_REC(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h ==> is_pr_sym (rec_sym g h).

    Both ``is_pr_sym`` hypotheses are vacuous: ``is_pr_sym``'s body
    accepts any (g, h) under the rec-sym tag (the closure property is
    enforced at the proof-system level via is_pr_def, not here).
    """
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h ==> is_pr_sym (rec_sym g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.fix("g h")
    p.assume("_h_pr: is_pr_sym g /\\ is_pr_sym h")
    rec_eq_th = p.unfold(REC_SYM_DEF, "g", "h")
    p.have(
        "rec_eq: rec_sym g h = "
        "Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 0)))) (Pair_ord g h)"
    ).by_thm(rec_eq_th)
    # Fresh bound names to avoid shadowing outer g, h.
    p.have(
        "h_ex: ?gg hh. rec_sym g h = "
        "Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 0)))) (Pair_ord gg hh)"
    ).by_exists(["g", "h"], "rec_eq")
    p.have(
        "h_body: " + _IS_PR_SYM_BODY.format(sym="rec_sym g h").replace(
            "?g h.", "?gg hh."
        ).replace("Pair_ord g h", "Pair_ord gg hh")
    ).by_disj("h_ex")
    p.thus("is_pr_sym (rec_sym g h)").by_unfold("h_body", IS_PR_SYM_DEF)


@proof
def PR_ARITY_ZERO(p):
    """|- pr_arity zero_sym = 0. STUB."""
    p.goal("pr_arity zero_sym = 0")
    p.sorry()


@proof
def PR_ARITY_ADJ(p):
    """|- pr_arity adj_sym = SUC0 (SUC0 0). STUB."""
    p.goal("pr_arity adj_sym = SUC0 (SUC0 0)")
    p.sorry()


@proof
def PR_ARITY_PROJ(p):
    """|- !i n. pr_arity (proj_sym i n) = n. STUB."""
    p.goal(
        "!i n. pr_arity (proj_sym i n) = n",
        types={"i": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


@proof
def PR_ARITY_IF_IN(p):
    """|- pr_arity if_in_sym = SUC0 (SUC0 (SUC0 (SUC0 0))). STUB."""
    p.goal("pr_arity if_in_sym = SUC0 (SUC0 (SUC0 (SUC0 0)))")
    p.sorry()


@proof
def PR_ARITY_REC(p):
    """|- !g h. pr_arity (rec_sym g h) = SUC0 (pr_arity g). STUB.

    (n+1)-ary rec on n-ary g; the +1 accounts for the recursion target.
    """
    p.goal(
        "!g h. pr_arity (rec_sym g h) = SUC0 (pr_arity g)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2A (d) -- the *defining equations* of the base layer as closed
# nat0 godelnums.
#
# Convention: free Var_t indices in a defining equation are *implicitly
# universally closed*. The defining-axiom godelnum is the open
# equation; the closure rule PROV_PRST_AXIOM combined with the
# generalisation rule produces the universal closure when needed; in
# practice consumers use the substitute-into-axiom derived rule (see
# PROV_PRST_SUBST_AXIOM in prst_proof) to specialise directly.
#
# Variable slot conventions (chosen once, reused across axioms):
#   Var_t 0           -- first formal argument
#   Var_t (SUC0 0)    -- second formal argument
#   Var_t (SUC0^2 0)  -- third / "y_vec" / "i" / extra
# These match the var_x / var_y / var_z constants from hf_proof, which
# pyzar re-uses for the nat0 encoding of PRST variables.
#
# Each closed nat0 below encodes one PR defining equation. The
# corresponding ``Prov_PRST (...)`` theorems live in prst_proof as
# one-line specialisations of PROV_PRST_AXIOM at this nat0.
# ---------------------------------------------------------------------------


# Closed: zero_sym applied to the empty argument list returns Empty_pt.
ZERO_DEF_AXIOM_DEF = define(
    "zero_def_axiom",
    parse_type("nat0"),
    "Eq_pf (App_pt zero_sym Empty_pt) Empty_pt",
)
zero_def_axiom = mk_const("zero_def_axiom", [])


# adj_sym is *primitive*: no defining equation. The term
# ``App_pt adj_sym (Tup_pt a (Tup_pt b Empty_pt))`` IS the adjunction
# operation, just as Empty_pt is the empty set. Adj_pt is a HOL-level
# abbreviation for callers' convenience -- it unfolds to the
# corresponding App_pt expression.
ADJ_PT_DEF = define(
    "Adj_pt",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\a:nat0. \\b:nat0. App_pt adj_sym (Tup_pt a (Tup_pt b Empty_pt))",
)
Adj_pt = mk_const("Adj_pt", [])


# Boolean encoding used by PR-symbol-valued predicates (e.g.
# Proof_PRST_pr returns T_pt iff its arguments form a valid proof).
# Lives here so prst_proof and prst_repr can both reference it.
#   T_pt := Adj_pt Empty_pt Empty_pt       ("encoded true",  tag 11)
#   F_pt := Empty_pt                       ("encoded false", tag 0)
T_PT_DEF = define("T_pt", parse_type("nat0"), "Adj_pt Empty_pt Empty_pt")
T_pt = mk_const("T_pt", [])

F_PT_DEF = define("F_pt", parse_type("nat0"), "Empty_pt")
F_pt = mk_const("F_pt", [])


# Helper: n-fold Var_t tuple used by proj_def_axiom_at's argument list.
# Built by primitive recursion on nat0:
#     var_t_args_rev 0           = Empty_pt
#     var_t_args_rev (SUC0 k)    = Tup_pt (Var_t k) (var_t_args_rev k).
# Result for n is the Tup_pt-nested tuple
#     Tup_pt (Var_t (n-1)) (Tup_pt (Var_t (n-2)) ... (Tup_pt (Var_t 0) Empty_pt)).
# (Reverse index order; the choice is consistent across rec / proj defining
# equations, so the soundness obligation is uniform.)
_k_var_args = Var("k", nat0_ty)
_a_var_args = Var("a", nat0_ty)
_h_var_t_args = mk_abs(
    _k_var_args,
    mk_abs(
        _a_var_args,
        mk_app(mk_app(mk_const("Tup_pt", []), mk_app(Var_t, _k_var_args)), _a_var_args),
    ),
)
VAR_T_ARGS_REV_BASE, VAR_T_ARGS_REV_STEP = define_unary_0(
    "var_t_args_rev",
    parse_type("nat0 -> nat0"),
    Empty_pt,
    _h_var_t_args,
    result_ty=nat0_ty,
)
var_t_args_rev = mk_const("var_t_args_rev", [])


# proj_sym i n is parametric in i, n at the HOL level: each (i, n) gives
# a distinct closed axiom. ``proj_def_axiom_at i n`` is the axiom
# godelnum for that specific (i, n) pair.
#
#   proj_def_axiom_at i n
#     := Eq_pf (App_pt (proj_sym i n) (var_t_args_rev n))
#              (Var_t i)
PROJ_DEF_AXIOM_AT_DEF = define(
    "proj_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\i:nat0. \\n:nat0. "
    "Eq_pf (App_pt (proj_sym i n) (var_t_args_rev n)) (Var_t i)",
)
proj_def_axiom_at = mk_const("proj_def_axiom_at", [])


# if_in_sym a b x y -- two branches, encoded as two implications.
#   if_in_true : In_pa a b -> if_in_sym(a, b, x, y) = x
#   if_in_false: ~ In_pa a b -> if_in_sym(a, b, x, y) = y
# Free Var_t 0..3 universally quantified.
IF_IN_TRUE_DEF_AXIOM_DEF = define(
    "if_in_true_def_axiom",
    parse_type("nat0"),
    "Imp_pf (In_pa (Var_t 0) (Var_t (SUC0 0))) "
    "       (Eq_pf (App_pt if_in_sym "
    "                (Tup_pt (Var_t 0) "
    "                  (Tup_pt (Var_t (SUC0 0)) "
    "                    (Tup_pt (Var_t (SUC0 (SUC0 0))) "
    "                      (Tup_pt (Var_t (SUC0 (SUC0 (SUC0 0)))) Empty_pt))))) "
    "              (Var_t (SUC0 (SUC0 0))))",
)
if_in_true_def_axiom = mk_const("if_in_true_def_axiom", [])


IF_IN_FALSE_DEF_AXIOM_DEF = define(
    "if_in_false_def_axiom",
    parse_type("nat0"),
    "Imp_pf (Not_pf (In_pa (Var_t 0) (Var_t (SUC0 0)))) "
    "       (Eq_pf (App_pt if_in_sym "
    "                (Tup_pt (Var_t 0) "
    "                  (Tup_pt (Var_t (SUC0 0)) "
    "                    (Tup_pt (Var_t (SUC0 (SUC0 0))) "
    "                      (Tup_pt (Var_t (SUC0 (SUC0 (SUC0 0)))) Empty_pt))))) "
    "              (Var_t (SUC0 (SUC0 (SUC0 0)))))",
)
if_in_false_def_axiom = mk_const("if_in_false_def_axiom", [])


# rec_sym g h is parametric in g, h. Each (g, h) pair gives two axioms
# (base and step), each a closed nat0 indexed by (g, h).
#
# Variable slot convention (within these axioms):
#     Var_t 0           : y_vec (the carried argument; a single slot
#                         stands in for the n-tuple of carried args
#                         when g/h have higher arity -- the arity
#                         correctness obligation lives at Layer 4)
#     Var_t (SUC0 0)    : i (the head of the recursion target's
#                         Adj decomposition)
#     Var_t (SUC0^2 0)  : s (the tail of the recursion target's
#                         Adj decomposition)
#
# rec_base: ``rec g h Empty_pt y_vec = g y_vec``.
REC_BASE_DEF_AXIOM_AT_DEF = define(
    "rec_base_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\g:nat0. \\h:nat0. "
    "Eq_pf (App_pt (rec_sym g h) (Tup_pt Empty_pt (Tup_pt (Var_t 0) Empty_pt))) "
    "      (App_pt g (Tup_pt (Var_t 0) Empty_pt))",
)
rec_base_def_axiom_at = mk_const("rec_base_def_axiom_at", [])


# rec_step: ``rec g h (Adj_pt i s) y_vec = h i s (rec g h s y_vec) y_vec``
# (the membership-canonical normalisation collapse case is handled at
# the proof-system level rather than syntactically here).
REC_STEP_DEF_AXIOM_AT_DEF = define(
    "rec_step_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\g:nat0. \\h:nat0. "
    "Eq_pf "
    "  (App_pt (rec_sym g h) "
    "     (Tup_pt (App_pt adj_sym "
    "                (Tup_pt (Var_t (SUC0 0)) "
    "                  (Tup_pt (Var_t (SUC0 (SUC0 0))) Empty_pt))) "
    "             (Tup_pt (Var_t 0) Empty_pt))) "
    "  (App_pt h "
    "     (Tup_pt (Var_t (SUC0 0)) "
    "       (Tup_pt (Var_t (SUC0 (SUC0 0))) "
    "         (Tup_pt (App_pt (rec_sym g h) "
    "                    (Tup_pt (Var_t (SUC0 (SUC0 0))) "
    "                      (Tup_pt (Var_t 0) Empty_pt))) "
    "           (Tup_pt (Var_t 0) Empty_pt)))))",
)
rec_step_def_axiom_at = mk_const("rec_step_def_axiom_at", [])


# ---------------------------------------------------------------------------
# Stage 2A (e) -- is_pr_def, the structural recogniser.
#
# Disjunction recognising any closed nat0 that matches one of the six
# defining-equation patterns (no adj branch since adj_sym is primitive).
#
# Stub body: F. Real body is the disjunction listed below. The
# IS_PR_DEF_HOLDS_* lemmas (one per axiom) discharge by tag analysis.
# ---------------------------------------------------------------------------


IS_PR_DEF_DEF = define(
    "is_pr_def",
    parse_type("nat0 -> bool"),
    # No adj branch: adj_sym is primitive, no defining equation.
    "\\n:nat0. "
    "n = zero_def_axiom \\/ "
    "(?i n0. n = proj_def_axiom_at i n0 /\\ nat0_lt i n0) \\/ "
    "n = if_in_true_def_axiom \\/ "
    "n = if_in_false_def_axiom \\/ "
    "(?g h. n = rec_base_def_axiom_at g h "
    "       /\\ is_pr_sym g /\\ is_pr_sym h) \\/ "
    "(?g h. n = rec_step_def_axiom_at g h "
    "       /\\ is_pr_sym g /\\ is_pr_sym h)",
)
is_pr_def = mk_const("is_pr_def", [])


# Same proof shape as the IS_PR_SYM_* lemmas: build the 6-disjunct body
# of IS_PR_DEF_DEF specialized at the axiom name, then by_unfold. The
# REFL cases (ZERO / IF_IN_TRUE / IF_IN_FALSE) discharge a literal-equal
# disjunct; PROJ / REC_BASE / REC_STEP build the 2-binder existential
# leaf via by_exists first (since by_disj_witness is single-binder).
# Fresh bound names (ii nn0 / gg hh) avoid the by_unfold alpha-rename
# trap from Layer 4 part 1.
_IS_PR_DEF_BODY = (
    "{n} = zero_def_axiom \\/ "
    "(?ii nn0. {n} = proj_def_axiom_at ii nn0 /\\ nat0_lt ii nn0) \\/ "
    "{n} = if_in_true_def_axiom \\/ "
    "{n} = if_in_false_def_axiom \\/ "
    "(?gg hh. {n} = rec_base_def_axiom_at gg hh "
    "         /\\ is_pr_sym gg /\\ is_pr_sym hh) \\/ "
    "(?gg hh. {n} = rec_step_def_axiom_at gg hh "
    "         /\\ is_pr_sym gg /\\ is_pr_sym hh)"
)


@proof
def IS_PR_DEF_HOLDS_ZERO(p):
    """|- is_pr_def zero_def_axiom."""
    from tactics import REFL
    p.goal("is_pr_def zero_def_axiom")
    p.have("h_refl: zero_def_axiom = zero_def_axiom").by_thm(
        REFL(p._parse("zero_def_axiom"))
    )
    p.have("h_body: " + _IS_PR_DEF_BODY.format(n="zero_def_axiom")).by_disj(
        "h_refl"
    )
    p.thus("is_pr_def zero_def_axiom").by_unfold("h_body", IS_PR_DEF_DEF)


@proof
def IS_PR_DEF_HOLDS_PROJ(p):
    """|- !i n. nat0_lt i n ==> is_pr_def (proj_def_axiom_at i n)."""
    from tactics import REFL
    p.goal(
        "!i n. nat0_lt i n ==> is_pr_def (proj_def_axiom_at i n)",
        types={"i": nat0_ty, "n": nat0_ty},
    )
    p.fix("i n")
    p.assume("h_lt: nat0_lt i n")
    p.have(
        "h_refl: proj_def_axiom_at i n = proj_def_axiom_at i n"
    ).by_thm(REFL(p._parse("proj_def_axiom_at i n")))
    # by_exists splits the body into conjuncts and discharges each via
    # a supplied rule (equation conjuncts also fall back to REWRITE_PROVE).
    # The non-equation `nat0_lt i n` conjunct needs `h_lt` to alpha-match.
    p.have(
        "h_ex: ?ii nn0. proj_def_axiom_at i n = proj_def_axiom_at ii nn0 "
        "      /\\ nat0_lt ii nn0"
    ).by_exists(["i", "n"], "h_refl", "h_lt")
    p.have(
        "h_body: " + _IS_PR_DEF_BODY.format(n="proj_def_axiom_at i n")
    ).by_disj("h_ex")
    p.thus("is_pr_def (proj_def_axiom_at i n)").by_unfold(
        "h_body", IS_PR_DEF_DEF
    )


@proof
def IS_PR_DEF_HOLDS_IF_IN_TRUE(p):
    """|- is_pr_def if_in_true_def_axiom."""
    from tactics import REFL
    p.goal("is_pr_def if_in_true_def_axiom")
    p.have("h_refl: if_in_true_def_axiom = if_in_true_def_axiom").by_thm(
        REFL(p._parse("if_in_true_def_axiom"))
    )
    p.have(
        "h_body: " + _IS_PR_DEF_BODY.format(n="if_in_true_def_axiom")
    ).by_disj("h_refl")
    p.thus("is_pr_def if_in_true_def_axiom").by_unfold(
        "h_body", IS_PR_DEF_DEF
    )


@proof
def IS_PR_DEF_HOLDS_IF_IN_FALSE(p):
    """|- is_pr_def if_in_false_def_axiom."""
    from tactics import REFL
    p.goal("is_pr_def if_in_false_def_axiom")
    p.have("h_refl: if_in_false_def_axiom = if_in_false_def_axiom").by_thm(
        REFL(p._parse("if_in_false_def_axiom"))
    )
    p.have(
        "h_body: " + _IS_PR_DEF_BODY.format(n="if_in_false_def_axiom")
    ).by_disj("h_refl")
    p.thus("is_pr_def if_in_false_def_axiom").by_unfold(
        "h_body", IS_PR_DEF_DEF
    )


@proof
def IS_PR_DEF_HOLDS_REC_BASE(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h
            ==> is_pr_def (rec_base_def_axiom_at g h)."""
    from tactics import REFL
    from tactics import CONJ
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h "
        "==> is_pr_def (rec_base_def_axiom_at g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.fix("g h")
    p.assume("(h_g, h_h): is_pr_sym g /\\ is_pr_sym h")
    p.have(
        "h_refl: rec_base_def_axiom_at g h = rec_base_def_axiom_at g h"
    ).by_thm(REFL(p._parse("rec_base_def_axiom_at g h")))
    p.have(
        "h_ex: ?gg hh. rec_base_def_axiom_at g h = rec_base_def_axiom_at gg hh "
        "      /\\ is_pr_sym gg /\\ is_pr_sym hh"
    ).by_exists(["g", "h"], "h_refl", "h_g", "h_h")
    p.have(
        "h_body: " + _IS_PR_DEF_BODY.format(n="rec_base_def_axiom_at g h")
    ).by_disj("h_ex")
    p.thus("is_pr_def (rec_base_def_axiom_at g h)").by_unfold(
        "h_body", IS_PR_DEF_DEF
    )


@proof
def IS_PR_DEF_HOLDS_REC_STEP(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h
            ==> is_pr_def (rec_step_def_axiom_at g h)."""
    from tactics import REFL
    from tactics import CONJ
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h "
        "==> is_pr_def (rec_step_def_axiom_at g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.fix("g h")
    p.assume("(h_g, h_h): is_pr_sym g /\\ is_pr_sym h")
    p.have(
        "h_refl: rec_step_def_axiom_at g h = rec_step_def_axiom_at g h"
    ).by_thm(REFL(p._parse("rec_step_def_axiom_at g h")))
    p.have(
        "h_ex: ?gg hh. rec_step_def_axiom_at g h = rec_step_def_axiom_at gg hh "
        "      /\\ is_pr_sym gg /\\ is_pr_sym hh"
    ).by_exists(["g", "h"], "h_refl", "h_g", "h_h")
    p.have(
        "h_body: " + _IS_PR_DEF_BODY.format(n="rec_step_def_axiom_at g h")
    ).by_disj("h_ex")
    p.thus("is_pr_def (rec_step_def_axiom_at g h)").by_unfold(
        "h_body", IS_PR_DEF_DEF
    )


# ---------------------------------------------------------------------------
# Stage 2A (f) -- the *PR introduction* combinator (sketch only).
#
# The base layer is "complete" in that every PR set function is
# expressible as a composition of {Zero, Adj, Proj, If_in, Rec}. So
# downstream PR functions -- substitute_pr, numeral_pr, diag_pr,
# Proof_PRST_pr -- can be defined as HOL functions that compute the
# composite ``f_sym`` from the base symbols, with no further axioms.
#
# Each derived symbol comes with a *derived* defining equation theorem:
#
#   Lemma (compose). For any PR symbols g, h_1, ..., h_k of compatible
#   arity, there exists a PR symbol comp(g, h_1, ..., h_k) such that
#       Prov_PRST (Eq_pf (App_pt (comp g h_1 ... h_k) args)
#                        (App_pt g (Tup_pt (App_pt h_1 args)
#                                            ...
#                                            (Tup_pt (App_pt h_k args)
#                                                    Empty_pt)))).
#
# In practice ``comp`` is itself a base-layer construction (REC over
# trivial recursion), so its defining equation reduces to PRST_REC_*
# instances. We expose ``comp_sym`` as a convenience.
# ---------------------------------------------------------------------------


comp_sym_def = define(
    "comp_sym",
    parse_type("nat0 -> nat0 -> nat0"),  # comp_sym g hs (hs is a list of symbols)
    "\\g:nat0. \\hs:nat0. Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))) "
    "                              (Pair_ord g hs)",
)
comp_sym = mk_const("comp_sym", [])


# PRST_COMP_DEF is a Prov_PRST claim about comp_sym; it lives in
# prst_proof to avoid the forward reference.


# ---------------------------------------------------------------------------
# Stage 2A (f') -- Kleene minimisation as an operator on PR symbols.
#
# mu_sym f  :=  the symbol id of the unary function
#                   args |-> least q s.t. App_pt f (Tup_pt q args) = T_pt,
#               or a sentinel if no such q exists.
#
# Crucially, mu_sym is an *operator on closed nat0 symbol ids*, not a
# binder on formulas. The witness variable lives inside mu_sym's
# meta-level interpretation; it never appears as a syntactic binder in
# any PRST term or formula. So substitute_p / free_in_p see only the
# App_pt clause they already handle, and no capture-avoidance machinery
# is needed for mu.
#
# Cost: mu_sym leaves strict primitive recursion. The standard nat0
# HOL model interprets mu_sym soundly via classical least-witness (with
# sentinel for the no-witness case), so consistency is preserved -- but
# the resulting symbol class "PR + mu" is total-recursive rather than
# PR. We mark this distinction with ``is_partial_pr_sym``: every
# is_pr_sym is is_partial_pr_sym, and mu_sym(f) is is_partial_pr_sym
# when f is.
# ---------------------------------------------------------------------------


mu_sym_def = define(
    "mu_sym",
    parse_type("nat0 -> nat0"),  # mu_sym f
    "\\f:nat0. Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))) f",
)
mu_sym = mk_const("mu_sym", [])


# is_partial_pr_sym extends is_pr_sym with the mu-closed symbols. The
# definition now lives in prst_syntax.py (Stage 1 d.5) because
# `_IS_PTERM_F_DEF`'s App-branch guard mentions is_partial_pr_sym;
# prst_syntax encodes the mu-disjunct using bare `Pair_ord 6 g`, and
# the bridge lemma IS_PARTIAL_PR_SYM_MU below packages
# `is_partial_pr_sym (mu_sym f)` from that body.
from prst_syntax import (  # noqa: E402
    is_partial_pr_sym,  # noqa: F401  -- re-export
    IS_PARTIAL_PR_SYM_DEF,  # noqa: F401  -- re-export
    _IS_PARTIAL_PR_SYM_REC,
    _IS_PARTIAL_PR_SYM_F_DEF,
    IS_PARTIAL_PR_SYM_MONO,  # noqa: F401  -- re-export
)


# NAT0_LT_MU_SYM: `mu_sym g = Pair_ord 6 g`, so `g < mu_sym g` by
# NAT0_LT_PAIR_ORD_R + unfold mu_sym. Kept here (alongside mu_sym
# itself) so prst_syntax stays mu-agnostic; consumed by
# IS_PARTIAL_PR_SYM_MU below.
@proof
def NAT0_LT_MU_SYM(p):
    """|- !g. nat0_lt g (mu_sym g)."""
    from hf_sets import NAT0_LT_PAIR_ORD_R
    p.goal("!g. nat0_lt g (mu_sym g)", types={"g": nat0_ty})
    p.fix("g")
    # mu_sym g = Pair_ord 6 g; nat0_lt g (Pair_ord 6 g) by NAT0_LT_PAIR_ORD_R.
    p.have("h_pair: nat0_lt g (Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))) g)").by(
        NAT0_LT_PAIR_ORD_R, "SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))", "g"
    )
    # Specialize mu_sym_def at g via p.unfold so the rewrite is on the
    # applied form (not the bare abstraction): |- mu_sym g = Pair_ord 6 g.
    mu_at_g = p.unfold(mu_sym_def, "g")
    p.thus("nat0_lt g (mu_sym g)").by_rewrite_of("h_pair", [SYM(mu_at_g)])


@proof
def IS_PARTIAL_PR_SYM_MU(p):
    """|- !f. is_partial_pr_sym f ==> is_partial_pr_sym (mu_sym f).

    Bridges from the prst_syntax-side encoding (`Pair_ord 6 g`) to the
    symbolic `mu_sym g` form. The wf-recursion body in prst_syntax says
    `is_partial_pr_sym f = is_pr_sym f \\/ (?g. f = Pair_ord 6 g /\\
    is_partial_pr_sym g)`. We hit the mu-branch with g := f and unfold
    mu_sym to bridge `Pair_ord 6 f = mu_sym f`.
    """
    from tactics import REFL, SPEC
    p.goal(
        "!f. is_partial_pr_sym f ==> is_partial_pr_sym (mu_sym f)",
        types={"f": nat0_ty},
    )
    p.fix("f")
    p.assume("h_part: is_partial_pr_sym f")
    # Bridge `mu_sym f = Pair_ord 6 f` from the abstraction equation.
    mu_at_f = p.unfold(mu_sym_def, "f")
    # mu_at_f: mu_sym f = Pair_ord 6 f.
    # Build the mu-branch of the body at n := mu_sym f, witness g := f.
    p.have(
        "h_eq: mu_sym f = Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))) f"
    ).by_thm(mu_at_f)
    p.have(
        "h_ex: ?gg. mu_sym f = Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))) gg "
        "        /\\ is_partial_pr_sym gg"
    ).by_exists(["f"], "h_eq", "h_part")
    # Disjunction body of _IS_PARTIAL_PR_SYM_F at n := mu_sym f.
    p.have(
        "h_body: is_pr_sym (mu_sym f) "
        "        \\/ (?gg. mu_sym f = Pair_ord (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))) gg "
        "                  /\\ is_partial_pr_sym gg)"
    ).by_disj("h_ex")
    # Bridge to _is_partial_pr_sym_F is_partial_pr_sym (mu_sym f).
    p.have(
        "h_F: _is_partial_pr_sym_F is_partial_pr_sym (mu_sym f)"
    ).by_unfold("h_body", _IS_PARTIAL_PR_SYM_F_DEF)
    # And to is_partial_pr_sym (mu_sym f) via the recursion equation.
    p.thus("is_partial_pr_sym (mu_sym f)").by_eq_mp(
        SYM(SPEC(p._parse("mu_sym f"), _IS_PARTIAL_PR_SYM_REC)),
        "h_F",
    )


# find_proof_pr := mu_sym Proof_PRST_pr -- the unbounded search for a
# proof of the second-argument formula. Defined later, after
# Proof_PRST_pr.


# ---------------------------------------------------------------------------
# Stage 2A (g) -- sketches of the four headline PR symbols.
#
# These are HOL-side definitions; their defining equations follow
# uniformly from PRST_REC_* / PRST_PROJ_* / PRST_ADJ_* / PRST_IF_IN_*.
#
# ``numeral_pr`` -- the symbol that, applied to n, returns the encoded
# numeral term ``numeral(n)`` (a nested Adj_pt tower). Definition:
#   numeral_pr := REC zero_sym (\i,s,r,_vec. ADJ r r)
# Defining equation:
#   numeral_pr 0           = Empty_pt
#   numeral_pr (Adj_pt i s) = Adj_pt (numeral_pr s) (numeral_pr s)
# (i.e. successor as von-Neumann ordinal). One Prov_PRST equation each;
# both discharged by PRST_REC_BASE / PRST_REC_STEP at concrete g, h.
#
# ``substitute_pr`` -- structural recursion on the formula tree.
# Five base-layer compositions, one per formula constructor; the
# App_pt recursive call uses ``map_substitute`` which is itself
# definable as a REC over the Tup_pt-nested args. Total: ~10 base-layer
# symbols composed, ~30 Prov_PRST defining equations.
#
# ``diag_pr`` -- two compositions:  diag(n) = substitute_pr(n,
# numeral_pr(n), var_x). HOL-level: comp_sym substitute_pr [proj_sym 0 1,
# comp_sym numeral_pr [proj_sym 0 1], const_sym var_x]. Defining
# equation: one Prov_PRST equation via PRST_COMP_DEF.
#
# ``Proof_PRST_pr`` -- decidable list-of-formulas proof checker; uses
# ``is_pr_axiom`` (= is_pr_def \/ is_logical_axiom) and ``is_mp``.
# All primitive recursive. Total: ~50 base-layer symbols composed.
#
# The full implementation is ~600 lines; PR symbols are first-class
# terms, so there are no trace sets and no functionality proofs.
# ---------------------------------------------------------------------------


# numeral_pr := REC zero_sym (\i,s,r,_vec. Adj_pt r r)
#            =  rec_sym zero_sym (comp_sym adj_sym (Tup_pt (proj 2 4)
#                                                    (Tup_pt (proj 2 4)
#                                                            Empty_pt)))
# 4-ary step (i, s, r, y_vec), zero-ary y_vec collapses to no
# additional slots; proj 2 4 picks ``r`` (the 3rd of 4 args).
numeral_pr_def = define(
    "numeral_pr",
    parse_type("nat0"),
    "rec_sym zero_sym "
    "  (comp_sym adj_sym "
    "    (Tup_pt (proj_sym (SUC0 (SUC0 0)) (SUC0 (SUC0 (SUC0 (SUC0 0))))) "
    "      (Tup_pt (proj_sym (SUC0 (SUC0 0)) (SUC0 (SUC0 (SUC0 (SUC0 0))))) "
    "        Empty_pt)))",
)
numeral_pr = mk_const("numeral_pr", [])


# substitute_pr -- structural recursion on the formula tree. The
# complete body is a comp_sym / rec_sym / if_in_sym chain (~100 lines)
# discriminating on each formula constructor (Empty / Var / Tup / Eq /
# In / Not / Imp / App) and recursing on subterms. Pending the full
# expansion, model it here as the identity-like 3-ary composition that
# returns its first argument -- well-typed and structurally valid, just
# not yet the intended function. Downstream lemmas (Layer 7
# PROV_PRST_SUBSTITUTE_EVAL) remain sorry'd against this placeholder.
substitute_pr_def = define(
    "substitute_pr",
    parse_type("nat0"),
    "proj_sym 0 (SUC0 (SUC0 (SUC0 0)))",
)
substitute_pr = mk_const("substitute_pr", [])


# diag_pr n := substitute_pr (n, numeral_pr n, var_x).
# Compositional shape: comp_sym substitute_pr applied to three 1-ary
# argument-shapers, each fed the original n:
#   * proj 0 1           -- yields n
#   * comp_sym numeral_pr (Tup_pt (proj 0 1) Empty_pt) -- yields numeral n
#   * const_var_x        -- yields var_x (constant function)
# PRST does not yet provide a const_sym primitive, so the var_x slot is
# left as a structural hole here; the third arg in the comp_sym arg-list
# is omitted. Layer 7 fills it in alongside the full substitute_pr body.
diag_pr_def = define(
    "diag_pr",
    parse_type("nat0"),
    "comp_sym substitute_pr "
    "  (Tup_pt (proj_sym 0 (SUC0 0)) "
    "    (Tup_pt (comp_sym numeral_pr "
    "               (Tup_pt (proj_sym 0 (SUC0 0)) Empty_pt)) "
    "      Empty_pt))",
)
diag_pr = mk_const("diag_pr", [])


# Proof_PRST_pr -- the list-of-formulas proof checker as a PR symbol.
# Full body is ~50 base-layer symbol compositions (case-split via
# if_in_sym on each axiom schema + modus-ponens recognition + recursion
# on the proof list). Sentinel composition pending full expansion: a
# 2-ary projection that returns its second argument, well-typed for
# inputs (proof_list, target_formula). Layer 7 / Layer 10 lemmas remain
# sorry'd against this placeholder.
Proof_PRST_pr_def = define(
    "Proof_PRST_pr",
    parse_type("nat0"),
    "proj_sym (SUC0 0) (SUC0 (SUC0 0))",
)
Proof_PRST_pr = mk_const("Proof_PRST_pr", [])


# find_proof_pr is the mu-closure of Proof_PRST_pr: applied to a formula
# godelnum x, it returns (a witness for) the least p such that
# Proof_PRST_pr checks (p, x) to T_pt -- equivalently, returns *some*
# proof of x when one exists.
FIND_PROOF_PR_DEF = define("find_proof_pr", parse_type("nat0"), "mu_sym Proof_PRST_pr")
find_proof_pr = mk_const("find_proof_pr", [])


# Defining equations for the headline derived symbols (numeral_pr,
# substitute_pr, diag_pr, Proof_PRST_pr) are Prov_PRST claims, so they
# live in prst_proof.py:
#
#     NUMERAL_PR_DEF_EQ_ZERO, NUMERAL_PR_DEF_EQ_SUC,
#     SUBSTITUTE_PR_DEFINING, DIAG_PR_DEFINING,
#     PROOF_PRST_PR_DEFINING.
#
# The mu-correctness axiom for find_proof_pr (and any mu-closed symbol)
# lives in prst_proof.py as MU_CORRECTNESS: from any specific witness
# q certifying f(q, args) = T_pt, conclude f(App_pt (mu_sym f) args,
# args) = T_pt. This is the only axiom about mu_sym -- it is what
# makes D2 derivable in the quantifier-free setting.


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 2A (PRST) -- PR-function-symbol registry.")
    print("    IS_PR_SYM_ZERO   :", pp_thm(IS_PR_SYM_ZERO))
    print("    IS_PR_SYM_ADJ    :", pp_thm(IS_PR_SYM_ADJ))
    print("    IS_PR_SYM_PROJ   :", pp_thm(IS_PR_SYM_PROJ))
    print("    IS_PR_SYM_IF_IN  :", pp_thm(IS_PR_SYM_IF_IN))
    print("    IS_PR_SYM_REC    :", pp_thm(IS_PR_SYM_REC))
    print()
    print("    PR_ARITY_ZERO    :", pp_thm(PR_ARITY_ZERO))
    print("    PR_ARITY_ADJ     :", pp_thm(PR_ARITY_ADJ))
    print("    PR_ARITY_PROJ    :", pp_thm(PR_ARITY_PROJ))
    print()
    print()
    print("Stage 2A (d) -- defining-equation godelnums (closed nat0s).")
    print("    ZERO_DEF_AXIOM_DEF        :", pp_thm(ZERO_DEF_AXIOM_DEF))
    print("    ADJ_PT_DEF                :", pp_thm(ADJ_PT_DEF))
    print("    IF_IN_TRUE_DEF_AXIOM_DEF  :", pp_thm(IF_IN_TRUE_DEF_AXIOM_DEF))
    print()
    print("Stage 2A (e) -- is_pr_def recogniser.")
    print("    IS_PR_DEF_DEF             :", pp_thm(IS_PR_DEF_DEF))
    print("    IS_PR_DEF_HOLDS_ZERO      :", pp_thm(IS_PR_DEF_HOLDS_ZERO))
    print("    IS_PR_DEF_HOLDS_PROJ      :", pp_thm(IS_PR_DEF_HOLDS_PROJ))
    print("    IS_PR_DEF_HOLDS_REC_BASE  :", pp_thm(IS_PR_DEF_HOLDS_REC_BASE))
    print()
    print("Prov_PRST claims about these axioms are one-line specialisations")
    print("of PROV_PRST_AXIOM in prst_proof.")

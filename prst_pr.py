# ---------------------------------------------------------------------------
# Stage 2A (PRST) -- the PR-function-symbol mechanism.
# ---------------------------------------------------------------------------
#
# Every primitive recursive function in PRST gets:
#
#   (i)   a closed nat0 ``f_sym`` -- its function-symbol id;
#   (ii)  one or more *defining equation* axioms, each of shape
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
    substitute_p,  # noqa: F401  -- parser alias for is_pr_def_instance
    suc_chain,
)
from prst_pr_builders import (  # tier-1 readable-body helpers
    nat, pt_list, proj, comp, rec, app_pt as _app_pt_b, var_t,
    eq_pf as _eq_pf_b, imp_pf as _imp_pf_b, in_pa as _in_pa_b,
    not_pf as _not_pf_b, tup_pt as _tup_pt_b,
    pair_ord as _pair_ord_b,
    adj_pt as _adj_pt_b,
)


# ---------------------------------------------------------------------------
# Stage 2A (a) -- the function-symbol registry.
#
#   * ``is_pr_sym f`` :  ``f`` is a registered PR-function symbol id.
# ``is_pr_sym`` is a HOL predicate on nat0. It is *defined* (not
# axiomatized) so that the introduction of new PR symbols is a kernel
# extension, not a fresh axiom. In practice each new symbol bumps a
# fresh value of ``is_pr_sym`` via constructor disjointness.
# ---------------------------------------------------------------------------


# is_pr_sym is defined in prst_syntax because IS_PTERM_AT_APP needs a
# forward reference before the concrete symbol constants are introduced.
from prst_syntax import is_pr_sym  # noqa: F401, E402


# ---------------------------------------------------------------------------
# Stage 2A (b) -- the base layer of PR symbols.
#
# Each symbol is a fresh closed nat0 id. The choice of id is irrelevant
# for downstream reasoning; ``IS_PR_SYM_*`` pins the registry entry.
# ---------------------------------------------------------------------------


ZERO_SYM_DEF = define("zero_sym", parse_type("nat0"), suc_chain(0))
zero_sym = mk_const("zero_sym", [])

ADJ_SYM_DEF = define("adj_sym", parse_type("nat0"), suc_chain(1))
adj_sym = mk_const("adj_sym", [])

PROJ_SYM_DEF = define(
    "proj_sym",
    parse_type("nat0 -> nat0 -> nat0"),
    f"\\i:nat0. \\n:nat0. Pair_ord ({suc_chain(2)}) (Pair_ord i n)",
)
proj_sym = mk_const("proj_sym", [])

IF_IN_SYM_DEF = define("if_in_sym", parse_type("nat0"), suc_chain(3))
if_in_sym = mk_const("if_in_sym", [])

REC_SYM_DEF = define(
    "rec_sym",
    parse_type("nat0 -> nat0 -> nat0"),
    f"\\g:nat0. \\h:nat0. Pair_ord ({suc_chain(4)}) (Pair_ord g h)",
)
rec_sym = mk_const("rec_sym", [])

# const_sym c -- the 1-ary PR symbol "constant function returning c".
# Tag 5 (between rec_sym tag 4 and mu_sym tag 6). Defining axiom:
#   App_pt (const_sym c) (Tup_pt (Var_t 0) Empty_pt) = c
# Closes the structural hole in diag_pr (the var_x slot) and unblocks
# any further "constant argument" plumbing in substitute_pr / etc.
CONST_SYM_DEF = define(
    "const_sym",
    parse_type("nat0 -> nat0"),
    f"\\c:nat0. Pair_ord ({suc_chain(5)}) c",
)
const_sym = mk_const("const_sym", [])

# course_rec_sym g h -- structural recursion on Pair_ord-decomposition.
# Tag 7 (skipping mu's tag 6). Encoded as Pair_ord 7 (Pair_ord g h),
# parametric in (g, h) like rec_sym: g is the base symbol (consulted at
# input 0), h is the step symbol (consulted at Pair_ord inputs).
#
# Defining axioms (one base + one step):
#   App_pt (course_rec g h) [0]            = App_pt g []
#   App_pt (course_rec g h) [Pair_ord a b]
#       = App_pt h [a; b;
#                   App_pt (course_rec g h) [a];
#                   App_pt (course_rec g h) [b]]
#
# The step's 4-tuple (a, b, rec_left, rec_right) gives h direct access
# to BOTH the destructured pieces and the recursive results at each,
# eliminating any need for separate pair_left / pair_right / get_tag
# primitives. Tag-dispatch happens inside h via if_in_sym against the
# bare literal "a" (which IS the constructor tag for Pair_ord-encoded
# inputs).
COURSE_REC_SYM_DEF = define(
    "course_rec_sym",
    parse_type("nat0 -> nat0 -> nat0"),
    f"\\g:nat0. \\h:nat0. Pair_ord ({suc_chain(7)}) (Pair_ord g h)",
)
course_rec_sym = mk_const("course_rec_sym", [])

# Pair_ord destructuring primitives at bare-literal tags 8 + 9 (course_rec
# took tag 7; mu_sym is tag 6). Non-parametric (no carried payload), same
# encoding shape as if_in_sym. Defining axioms (parametric in HOL-level
# pair components a, b):
#   App_pt pair_left_sym  (Tup_pt (Pair_ord a b) Empty_pt) = a
#   App_pt pair_right_sym (Tup_pt (Pair_ord a b) Empty_pt) = b
# Needed for the non-uniform App_pt case of substitute_pr (extract fn from
# Pair_ord fn args while course_rec only descends uniformly), and for the
# axiom-family pattern recognisers in Proof_PRST_pr's is_pr_axiom_pr.
PAIR_LEFT_SYM_DEF = define(
    "pair_left_sym",
    parse_type("nat0"),
    suc_chain(8),
)
pair_left_sym = mk_const("pair_left_sym", [])

PAIR_RIGHT_SYM_DEF = define(
    "pair_right_sym",
    parse_type("nat0"),
    suc_chain(9),
)
pair_right_sym = mk_const("pair_right_sym", [])

# pair_ord_sym -- 2-ary Pair_ord constructor. Symmetric counterpart of
# pair_left_sym / pair_right_sym (destructors). Encoded as bare literal
# SUC0^10 0 = 10. Defining axiom:
#   App_pt pair_ord_sym (Tup_pt a (Tup_pt b Empty_pt)) = Pair_ord a b
# Needed for substitute_pr's outer composer to package (t, v) into a
# single y_vec slot at PR level. Without it, the only path is to
# re-encode substitute_pr's external interface as 1-ary with caller
# pre-packing -- but diag_pr would still need PR-level pair construction
# to feed substitute_pr, so the construct primitive is load-bearing.
PAIR_ORD_SYM_DEF = define(
    "pair_ord_sym",
    parse_type("nat0"),
    suc_chain(10),
)
pair_ord_sym = mk_const("pair_ord_sym", [])


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
    f"{{sym}} = {suc_chain(1)} \\/ "
    f"(?i n. {{sym}} = Pair_ord ({suc_chain(2)}) (Pair_ord i n)) \\/ "
    f"{{sym}} = {suc_chain(3)} \\/ "
    f"(?g h. {{sym}} = Pair_ord ({suc_chain(4)}) (Pair_ord g h)) \\/ "
    f"(?c. {{sym}} = Pair_ord ({suc_chain(5)}) c) \\/ "
    f"(?g h. {{sym}} = Pair_ord ({suc_chain(7)}) (Pair_ord g h)) \\/ "
    f"{{sym}} = {suc_chain(8)} \\/ "
    f"{{sym}} = {suc_chain(9)} \\/ "
    f"{{sym}} = {suc_chain(10)}"
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
    p.have(f"adj_eq: adj_sym = {suc_chain(1)}").by_thm(ADJ_SYM_DEF)
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
        f"proj_eq: proj_sym i n = Pair_ord ({suc_chain(2)}) (Pair_ord i n)"
    ).by_thm(proj_eq_th)
    # DSL friction: by_disj_witness is single-binder; the existential
    # leaf here is `?i n. ...` (two binders), so we prove the
    # existential first via by_exists and then DISJ it in.
    # Use fresh bound names `ii nn` to avoid shadowing the outer i, n
    # (otherwise by_unfold's alpha-match misses the unfolded `i' n'`).
    p.have(
        f"h_ex: ?ii nn. proj_sym i n = Pair_ord ({suc_chain(2)}) (Pair_ord ii nn)"
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
    p.have(f"if_in_eq: if_in_sym = {suc_chain(3)}").by_thm(IF_IN_SYM_DEF)
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
        f"rec_eq: rec_sym g h = Pair_ord ({suc_chain(4)}) (Pair_ord g h)"
    ).by_thm(rec_eq_th)
    # Fresh bound names to avoid shadowing outer g, h.
    p.have(
        f"h_ex: ?gg hh. rec_sym g h = Pair_ord ({suc_chain(4)}) (Pair_ord gg hh)"
    ).by_exists(["g", "h"], "rec_eq")
    p.have(
        "h_body: " + _IS_PR_SYM_BODY.format(sym="rec_sym g h").replace(
            "?g h.", "?gg hh."
        ).replace("Pair_ord g h", "Pair_ord gg hh")
    ).by_disj("h_ex")
    p.thus("is_pr_sym (rec_sym g h)").by_unfold("h_body", IS_PR_SYM_DEF)


@proof
def IS_PR_SYM_CONST(p):
    """|- !c. is_pr_sym (const_sym c).

    `const_sym c = Pair_ord 5 c` (CONST_SYM_DEF), so the const-disjunct
    of `is_pr_sym`'s body matches at the witness `cc := c`.
    """
    p.goal("!c. is_pr_sym (const_sym c)", types={"c": nat0_ty})
    p.fix("c")
    const_eq_th = p.unfold(CONST_SYM_DEF, "c")
    p.have(
        f"const_eq: const_sym c = Pair_ord ({suc_chain(5)}) c"
    ).by_thm(const_eq_th)
    # Fresh bound name `cc` to avoid alpha-collision with the outer `c`.
    p.have(
        f"h_ex: ?cc. const_sym c = Pair_ord ({suc_chain(5)}) cc"
    ).by_exists(["c"], "const_eq")
    # Inline body string: same shape as _IS_PR_SYM_BODY but with the
    # const-disjunct binder renamed `?cc` to avoid alpha-collision with
    # outer `c`. (A naive _IS_PR_SYM_BODY.format(sym="const_sym c") would
    # rebind `?c` to the outer name.)
    body = (
        "const_sym c = 0 \\/ "
        f"const_sym c = {suc_chain(1)} \\/ "
        f"(?i n. const_sym c = Pair_ord ({suc_chain(2)}) (Pair_ord i n)) \\/ "
        f"const_sym c = {suc_chain(3)} \\/ "
        f"(?g h. const_sym c = Pair_ord ({suc_chain(4)}) (Pair_ord g h)) \\/ "
        f"(?cc. const_sym c = Pair_ord ({suc_chain(5)}) cc) \\/ "
        f"(?g h. const_sym c = Pair_ord ({suc_chain(7)}) (Pair_ord g h)) \\/ "
        f"const_sym c = {suc_chain(8)} \\/ "
        f"const_sym c = {suc_chain(9)} \\/ "
        f"const_sym c = {suc_chain(10)}"
    )
    p.have("h_body: " + body).by_disj("h_ex")
    p.thus("is_pr_sym (const_sym c)").by_unfold("h_body", IS_PR_SYM_DEF)


@proof
def IS_PR_SYM_COURSE_REC(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h ==> is_pr_sym (course_rec_sym g h).

    `course_rec_sym g h = Pair_ord 7 (Pair_ord g h)`; same 2-binder
    existential shape as IS_PR_SYM_REC. The hypotheses are vacuous at
    this layer (is_pr_sym's body has no closure requirements; closure
    is enforced at the proof-system level via is_pr_def).
    """
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h ==> is_pr_sym (course_rec_sym g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.fix("g h")
    p.assume("_h_pr: is_pr_sym g /\\ is_pr_sym h")
    course_eq_th = p.unfold(COURSE_REC_SYM_DEF, "g", "h")
    p.have(
        f"course_eq: course_rec_sym g h = Pair_ord ({suc_chain(7)}) (Pair_ord g h)"
    ).by_thm(course_eq_th)
    # Fresh bound names to avoid shadowing the outer g, h.
    p.have(
        f"h_ex: ?gg hh. course_rec_sym g h "
        f"= Pair_ord ({suc_chain(7)}) (Pair_ord gg hh)"
    ).by_exists(["g", "h"], "course_eq")
    # IS_PR_SYM_BODY's rec disjunct also has `?g h.`/`Pair_ord g h`, so
    # the substring replaces touch *both* the rec and course_rec
    # disjuncts. That's harmless: by_disj only needs each disjunct
    # well-formed; binder reuse is fine.
    p.have(
        "h_body: " + _IS_PR_SYM_BODY.format(sym="course_rec_sym g h").replace(
            "?g h.", "?gg hh."
        ).replace("Pair_ord g h", "Pair_ord gg hh")
    ).by_disj("h_ex")
    p.thus("is_pr_sym (course_rec_sym g h)").by_unfold(
        "h_body", IS_PR_SYM_DEF
    )


@proof
def IS_PR_SYM_PAIR_LEFT(p):
    """|- is_pr_sym pair_left_sym.

    ``pair_left_sym = SUC0^8 0`` (PAIR_LEFT_SYM_DEF); bare-literal
    disjunct in is_pr_sym's body, same shape as IS_PR_SYM_IF_IN.
    """
    p.goal("is_pr_sym pair_left_sym")
    p.have(f"eq: pair_left_sym = {suc_chain(8)}").by_thm(PAIR_LEFT_SYM_DEF)
    p.have("h_body: " + _IS_PR_SYM_BODY.format(sym="pair_left_sym")).by_disj(
        "eq"
    )
    p.thus("is_pr_sym pair_left_sym").by_unfold("h_body", IS_PR_SYM_DEF)


@proof
def IS_PR_SYM_PAIR_RIGHT(p):
    """|- is_pr_sym pair_right_sym."""
    p.goal("is_pr_sym pair_right_sym")
    p.have(f"eq: pair_right_sym = {suc_chain(9)}").by_thm(PAIR_RIGHT_SYM_DEF)
    p.have("h_body: " + _IS_PR_SYM_BODY.format(sym="pair_right_sym")).by_disj(
        "eq"
    )
    p.thus("is_pr_sym pair_right_sym").by_unfold("h_body", IS_PR_SYM_DEF)


@proof
def IS_PR_SYM_PAIR_ORD(p):
    """|- is_pr_sym pair_ord_sym."""
    p.goal("is_pr_sym pair_ord_sym")
    p.have(f"eq: pair_ord_sym = {suc_chain(10)}").by_thm(PAIR_ORD_SYM_DEF)
    p.have("h_body: " + _IS_PR_SYM_BODY.format(sym="pair_ord_sym")).by_disj(
        "eq"
    )
    p.thus("is_pr_sym pair_ord_sym").by_unfold("h_body", IS_PR_SYM_DEF)


# ---------------------------------------------------------------------------
# Stage 2A (d) -- the *defining equations* of the base layer as closed
# nat0 godelnums.
#
# Convention: free Var_t indices in a defining equation are *implicitly
# universally closed*. The defining-axiom godelnum is the open
# equation; the closure rule PROV_PRST_AX combined with the
# generalisation rule produces the universal closure when needed; in
# practice consumers use the substitute-into-axiom derived rule (see
# PROV_PRST_SUBST in prst_proof) to specialise directly.
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
# one-line specialisations of PROV_PRST_AX at this nat0.
# ---------------------------------------------------------------------------


# Closed: zero_sym applied to the empty argument list returns Empty_pt.
# `_app_pt_b` with no args builds `App_pt zero_sym Empty_pt`.
ZERO_DEF_AXIOM_DEF = define(
    "zero_def_axiom",
    parse_type("nat0"),
    _eq_pf_b(_app_pt_b(zero_sym), Empty_pt),
)
zero_def_axiom = mk_const("zero_def_axiom", [])


# adj_sym is *primitive*: no defining equation. The term
# ``App_pt adj_sym (Tup_pt a (Tup_pt b Empty_pt))`` IS the adjunction
# operation, just as Empty_pt is the empty set. Adj_pt is a HOL-level
# abbreviation for callers' convenience -- it unfolds to the
# corresponding App_pt expression.
_a_var_adj = Var("a", nat0_ty)
_b_var_adj = Var("b", nat0_ty)
ADJ_PT_DEF = define(
    "Adj_pt",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(_a_var_adj, mk_abs(_b_var_adj,
        _app_pt_b(adj_sym, _a_var_adj, _b_var_adj),
    )),
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


@proof
def T_PT_NEQ_F_PT(p):
    """|- ~(T_pt = F_pt).

    T_pt unfolds to `App_pt adj_sym (Tup_pt Empty_pt (Tup_pt Empty_pt Empty_pt))`
    via T_PT_DEF then ADJ_PT_DEF; F_pt unfolds to Empty_pt; the App_pt /
    Empty_pt disjointness comes from APP_PT_NEQ_EMPTY_PT. Lives here so
    downstream modules (prst_proof, prst_repr) can reuse it without an
    inline rebuild.
    """
    from tactics import TRANS
    from prst_syntax import APP_PT_NEQ_EMPTY_PT

    p.goal("~(T_pt = F_pt)")
    adj_at = p.unfold(ADJ_PT_DEF, "Empty_pt", "Empty_pt")
    t_at = TRANS(T_PT_DEF, adj_at)
    p.have(
        "h_app_neq: "
        "~(App_pt adj_sym (Tup_pt Empty_pt (Tup_pt Empty_pt Empty_pt)) = Empty_pt)"
    ).by(
        APP_PT_NEQ_EMPTY_PT,
        "adj_sym",
        "Tup_pt Empty_pt (Tup_pt Empty_pt Empty_pt)",
    )
    p.thus("~(T_pt = F_pt)").by_rewrite_of("h_app_neq", [t_at, F_PT_DEF])


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
# `proj_t(i, n)` (non-literal i, n -- already terms) is used because the
# lambda binds them as free Vars, not Python integers.
_i_var = Var("i", nat0_ty)
_n_var = Var("n", nat0_ty)
from prst_pr_builders import proj_t as _proj_t  # noqa: E402
PROJ_DEF_AXIOM_AT_DEF = define(
    "proj_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(_i_var, mk_abs(_n_var,
        _eq_pf_b(
            mk_app(App_pt, _proj_t(_i_var, _n_var), mk_app(var_t_args_rev, _n_var)),
            mk_app(Var_t, _i_var),
        ),
    )),
)
proj_def_axiom_at = mk_const("proj_def_axiom_at", [])


# if_in_sym a b x y -- two branches, encoded as two implications.
#   if_in_true : In_pa a b -> if_in_sym(a, b, x, y) = x
#   if_in_false: ~ In_pa a b -> if_in_sym(a, b, x, y) = y
# Free Var_t 0..3 universally quantified.
# if_in_true_def_axiom :=
#   In_pa Var_t0 Var_t1
#     ==> Eq_pf (App_pt if_in_sym [Var_t0; Var_t1; Var_t2; Var_t3]) Var_t2.
IF_IN_TRUE_DEF_AXIOM_DEF = define(
    "if_in_true_def_axiom",
    parse_type("nat0"),
    _imp_pf_b(
        _in_pa_b(var_t(0), var_t(1)),
        _eq_pf_b(
            _app_pt_b(if_in_sym, var_t(0), var_t(1), var_t(2), var_t(3)),
            var_t(2),
        ),
    ),
)
if_in_true_def_axiom = mk_const("if_in_true_def_axiom", [])


# Same shape as the true-branch but with `Not_pf` on the In_pa antecedent
# and Var_t 3 (the else-result) on the RHS.
IF_IN_FALSE_DEF_AXIOM_DEF = define(
    "if_in_false_def_axiom",
    parse_type("nat0"),
    _imp_pf_b(
        _not_pf_b(_in_pa_b(var_t(0), var_t(1))),
        _eq_pf_b(
            _app_pt_b(if_in_sym, var_t(0), var_t(1), var_t(2), var_t(3)),
            var_t(3),
        ),
    ),
)
if_in_false_def_axiom = mk_const("if_in_false_def_axiom", [])


# rec_sym g h is parametric in g, h. Each (g, h) pair gives two axioms
# (base and step), each a closed nat0 indexed by (g, h).
#
# Variable slot convention (within these axioms):
#     Var_t 0           : y_vec (the carried argument; a single slot
#                         stands in for the n-tuple of carried args
#                         when g/h consume tuple payloads)
#     Var_t (SUC0 0)    : i (the head of the recursion target's
#                         Adj decomposition)
#     Var_t (SUC0^2 0)  : s (the tail of the recursion target's
#                         Adj decomposition)
#
# rec_base: ``rec g h Empty_pt y_vec = g y_vec``.
#   Var_t 0 is y_vec; the empty list arg is Empty_pt directly.
_g_var = Var("g", nat0_ty)
_h_var = Var("h", nat0_ty)
REC_BASE_DEF_AXIOM_AT_DEF = define(
    "rec_base_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(_g_var, mk_abs(_h_var,
        _eq_pf_b(
            _app_pt_b(rec(_g_var, _h_var), Empty_pt, var_t(0)),
            _app_pt_b(_g_var, var_t(0)),
        ),
    )),
)
rec_base_def_axiom_at = mk_const("rec_base_def_axiom_at", [])


# rec_step: ``rec g h (Adj_pt i s) y_vec = h i s (rec g h s y_vec) y_vec``
#   Var_t 0 = y_vec, Var_t 1 = i, Var_t 2 = s.
# (The membership-canonical normalisation collapse case is handled at
# the proof-system level rather than syntactically here.)
REC_STEP_DEF_AXIOM_AT_DEF = define(
    "rec_step_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(_g_var, mk_abs(_h_var,
        _eq_pf_b(
            _app_pt_b(
                rec(_g_var, _h_var),
                _app_pt_b(adj_sym, var_t(1), var_t(2)),
                var_t(0),
            ),
            _app_pt_b(
                _h_var,
                var_t(1),
                var_t(2),
                _app_pt_b(rec(_g_var, _h_var), var_t(2), var_t(0)),
                var_t(0),
            ),
        ),
    )),
)
rec_step_def_axiom_at = mk_const("rec_step_def_axiom_at", [])


# const_def_axiom_at c: defining equation for const_sym c. Unary axiom
# (Var_t 0 is the single ignored arg). No side condition on c.
_c_var_const_ax = Var("c", nat0_ty)
CONST_DEF_AXIOM_AT_DEF = define(
    "const_def_axiom_at",
    parse_type("nat0 -> nat0"),
    mk_abs(_c_var_const_ax,
        _eq_pf_b(
            _app_pt_b(mk_app(const_sym, _c_var_const_ax), var_t(0)),
            _c_var_const_ax,
        ),
    ),
)
const_def_axiom_at = mk_const("const_def_axiom_at", [])


# course_rec defining-equation axioms. Two axioms (base + step),
# parametric like rec_*, with a y_vec slot (Var_t 0) for carrying
# auxiliary args through every recursion level. The y_vec slot lets
# downstream symbols like substitute_pr thread (t, v) through formula
# recursion without packaging them into the recursion target.
#
#   course_rec_base_def_axiom_at g h
#     := Eq_pf (App_pt (course_rec g h) (Tup_pt 0 (Tup_pt (Var_t 0) Empty_pt)))
#              (App_pt g (Tup_pt (Var_t 0) Empty_pt))
#
# The step is parametric in (g, h, a, b) -- the HOL-level pair
# components a, b are plugged directly into the encoded equation as
# the concrete Pair_ord shape. y_vec (Var_t 0) is threaded into every
# recursive call AND into the step function h:
#
#   course_rec_step_def_axiom_at g h a b
#     := Eq_pf (App_pt (course_rec g h) (Tup_pt (Pair_ord a b)
#                                              (Tup_pt (Var_t 0) Empty_pt)))
#              (App_pt h (Tup_pt a (Tup_pt b
#                          (Tup_pt (App_pt (course_rec g h)
#                                          (Tup_pt a (Tup_pt (Var_t 0)
#                                                            Empty_pt)))
#                          (Tup_pt (App_pt (course_rec g h)
#                                          (Tup_pt b (Tup_pt (Var_t 0)
#                                                            Empty_pt)))
#                          (Tup_pt (Var_t 0) Empty_pt))))))
#
# h is 5-ary: (a, b, rec_a, rec_b, y_vec). The step's 4-binder
# structure (g, h, a, b) at IS_PR_DEF level is new vs. rec_*'s 2-binder
# shape; by_exists generalises to the 4-witness case via the existing
# ``by_exists([...], rules)`` API.
def _course_rec_app(g_term, h_term, arg_term, y_term):
    """Helper: ``App_pt (course_rec_sym g h) (Tup_pt arg (Tup_pt y Empty_pt))``
    -- the common shape inside both base and step axiom RHSs."""
    return mk_app(
        mk_app(App_pt, mk_app(mk_app(course_rec_sym, g_term), h_term)),
        pt_list(arg_term, y_term),
    )


COURSE_REC_BASE_DEF_AXIOM_AT_DEF = define(
    "course_rec_base_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(_g_var, mk_abs(_h_var,
        _eq_pf_b(
            _course_rec_app(_g_var, _h_var, nat(0), var_t(0)),
            _app_pt_b(_g_var, var_t(0)),
        ),
    )),
)
course_rec_base_def_axiom_at = mk_const("course_rec_base_def_axiom_at", [])


_a_var_crec = Var("a", nat0_ty)
_b_var_crec = Var("b", nat0_ty)
COURSE_REC_STEP_DEF_AXIOM_AT_DEF = define(
    "course_rec_step_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0 -> nat0 -> nat0"),
    mk_abs(_g_var, mk_abs(_h_var, mk_abs(_a_var_crec, mk_abs(_b_var_crec,
        _eq_pf_b(
            _course_rec_app(_g_var, _h_var,
                            _pair_ord_b(_a_var_crec, _b_var_crec),
                            var_t(0)),
            _app_pt_b(
                _h_var,
                _a_var_crec,
                _b_var_crec,
                _course_rec_app(_g_var, _h_var, _a_var_crec, var_t(0)),
                _course_rec_app(_g_var, _h_var, _b_var_crec, var_t(0)),
                var_t(0),
            ),
        ),
    )))),
)
course_rec_step_def_axiom_at = mk_const("course_rec_step_def_axiom_at", [])


# pair_left / pair_right defining-equation axioms. Parametric in HOL-level
# (a, b) -- the pair components are plugged directly into the encoded
# equation as the concrete Pair_ord shape. No formal Var_t arg slot needed
# (the singleton input list contains the concrete Pair_ord directly).
#
#   pair_left_def_axiom_at a b
#     := Eq_pf (App_pt pair_left_sym  (Tup_pt (Pair_ord a b) Empty_pt)) a
#   pair_right_def_axiom_at a b
#     := Eq_pf (App_pt pair_right_sym (Tup_pt (Pair_ord a b) Empty_pt)) b
PAIR_LEFT_DEF_AXIOM_AT_DEF = define(
    "pair_left_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(_a_var_crec, mk_abs(_b_var_crec,
        _eq_pf_b(
            _app_pt_b(pair_left_sym,
                      _pair_ord_b(_a_var_crec, _b_var_crec)),
            _a_var_crec,
        ),
    )),
)
pair_left_def_axiom_at = mk_const("pair_left_def_axiom_at", [])

PAIR_RIGHT_DEF_AXIOM_AT_DEF = define(
    "pair_right_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(_a_var_crec, mk_abs(_b_var_crec,
        _eq_pf_b(
            _app_pt_b(pair_right_sym,
                      _pair_ord_b(_a_var_crec, _b_var_crec)),
            _b_var_crec,
        ),
    )),
)
pair_right_def_axiom_at = mk_const("pair_right_def_axiom_at", [])


# pair_ord defining-equation axiom. Parametric in HOL-level (a, b) like
# pair_left/right. Says: applied to the 2-arg list [a; b], pair_ord_sym
# returns Pair_ord a b.
#
#   pair_ord_def_axiom_at a b
#     := Eq_pf (App_pt pair_ord_sym (Tup_pt a (Tup_pt b Empty_pt)))
#              (Pair_ord a b)
PAIR_ORD_DEF_AXIOM_AT_DEF = define(
    "pair_ord_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(_a_var_crec, mk_abs(_b_var_crec,
        _eq_pf_b(
            mk_app(mk_app(App_pt, pair_ord_sym),
                   pt_list(_a_var_crec, _b_var_crec)),
            _pair_ord_b(_a_var_crec, _b_var_crec),
        ),
    )),
)
pair_ord_def_axiom_at = mk_const("pair_ord_def_axiom_at", [])


# ---------------------------------------------------------------------------
# Stage 2A (e) -- is_pr_def, the structural recogniser.
#
# Disjunction recognising any closed nat0 that matches one of the seven
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
    "       /\\ is_pr_sym g /\\ is_pr_sym h) \\/ "
    "(?c. n = const_def_axiom_at c) \\/ "
    "(?g h. n = course_rec_base_def_axiom_at g h "
    "       /\\ is_pr_sym g /\\ is_pr_sym h) \\/ "
    "(?g h a b. n = course_rec_step_def_axiom_at g h a b "
    "       /\\ is_pr_sym g /\\ is_pr_sym h) \\/ "
    "(?a b. n = pair_left_def_axiom_at a b) \\/ "
    "(?a b. n = pair_right_def_axiom_at a b) \\/ "
    "(?a b. n = pair_ord_def_axiom_at a b)",
)
is_pr_def = mk_const("is_pr_def", [])


IS_PR_DEF_INSTANCE_DEF, IS_PR_DEF_INSTANCE_AT = define_with_at(
    "is_pr_def_instance",
    parse_type("nat0 -> bool"),
    "\\n:nat0. is_pr_def n \\/ "
    "(?F t v. is_pr_def F /\\ n = substitute_p F t v)",
)
is_pr_def_instance = mk_const("is_pr_def_instance", [])


@proof
def IS_PR_DEF_INSTANCE_FROM_DEF(p):
    """|- !n. is_pr_def n ==> is_pr_def_instance n."""
    p.goal("!n. is_pr_def n ==> is_pr_def_instance n", types={"n": nat0_ty})
    p.fix("n")
    p.assume("h_def: is_pr_def n")
    p.have(
        "h_body: is_pr_def n \\/ "
        "(?F t v. is_pr_def F /\\ n = substitute_p F t v)"
    ).by_disj("h_def")
    p.thus("is_pr_def_instance n").by_unfold(
        "h_body", IS_PR_DEF_INSTANCE_DEF
    )


@proof
def IS_PR_DEF_INSTANCE_SUBST(p):
    """|- !F t v. is_pr_def F ==> is_pr_def_instance (substitute_p F t v)."""
    from tactics import REFL

    p.goal(
        "!F t v. is_pr_def F ==> is_pr_def_instance (substitute_p F t v)",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.fix("F t v")
    p.assume("h_def: is_pr_def F")
    p.have(
        "h_refl: substitute_p F t v = substitute_p F t v"
    ).by_thm(REFL(p._parse("substitute_p F t v")))
    p.have(
        "h_ex: ?F0 t0 v0. is_pr_def F0 "
        "      /\\ substitute_p F t v = substitute_p F0 t0 v0"
    ).by_exists(["F", "t", "v"], "h_def", "h_refl")
    p.have(
        "h_body: is_pr_def (substitute_p F t v) \\/ "
        "(?F0 t0 v0. is_pr_def F0 "
        " /\\ substitute_p F t v = substitute_p F0 t0 v0)"
    ).by_disj("h_ex")
    p.thus("is_pr_def_instance (substitute_p F t v)").by_unfold(
        "h_body", IS_PR_DEF_INSTANCE_DEF
    )


# Same proof shape as the IS_PR_SYM_* lemmas: build the 7-disjunct body
# of IS_PR_DEF_DEF specialized at the axiom name, then by_unfold. The
# REFL cases (ZERO / IF_IN_TRUE / IF_IN_FALSE) discharge a literal-equal
# disjunct; PROJ / REC_BASE / REC_STEP build the 2-binder existential
# leaf via by_exists first (since by_disj_witness is single-binder);
# CONST is a single-binder existential like PROJ but unguarded.
# Fresh bound names (ii nn0 / gg hh / cc) avoid the by_unfold alpha-
# rename trap from Layer 4 part 1.
_IS_PR_DEF_BODY = (
    "{n} = zero_def_axiom \\/ "
    "(?ii nn0. {n} = proj_def_axiom_at ii nn0 /\\ nat0_lt ii nn0) \\/ "
    "{n} = if_in_true_def_axiom \\/ "
    "{n} = if_in_false_def_axiom \\/ "
    "(?gg hh. {n} = rec_base_def_axiom_at gg hh "
    "         /\\ is_pr_sym gg /\\ is_pr_sym hh) \\/ "
    "(?gg hh. {n} = rec_step_def_axiom_at gg hh "
    "         /\\ is_pr_sym gg /\\ is_pr_sym hh) \\/ "
    "(?cc. {n} = const_def_axiom_at cc) \\/ "
    "(?gg hh. {n} = course_rec_base_def_axiom_at gg hh "
    "         /\\ is_pr_sym gg /\\ is_pr_sym hh) \\/ "
    "(?gg hh aa bb. {n} = course_rec_step_def_axiom_at gg hh aa bb "
    "         /\\ is_pr_sym gg /\\ is_pr_sym hh) \\/ "
    "(?aa bb. {n} = pair_left_def_axiom_at aa bb) \\/ "
    "(?aa bb. {n} = pair_right_def_axiom_at aa bb) \\/ "
    "(?aa bb. {n} = pair_ord_def_axiom_at aa bb)"
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


@proof
def IS_PR_DEF_HOLDS_COURSE_REC_BASE(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h
            ==> is_pr_def (course_rec_base_def_axiom_at g h).

    Same 2-binder shape as IS_PR_DEF_HOLDS_REC_BASE.
    """
    from tactics import REFL
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h "
        "==> is_pr_def (course_rec_base_def_axiom_at g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.fix("g h")
    p.assume("(h_g, h_h): is_pr_sym g /\\ is_pr_sym h")
    p.have(
        "h_refl: course_rec_base_def_axiom_at g h = course_rec_base_def_axiom_at g h"
    ).by_thm(REFL(p._parse("course_rec_base_def_axiom_at g h")))
    p.have(
        "h_ex: ?gg hh. course_rec_base_def_axiom_at g h "
        "      = course_rec_base_def_axiom_at gg hh "
        "      /\\ is_pr_sym gg /\\ is_pr_sym hh"
    ).by_exists(["g", "h"], "h_refl", "h_g", "h_h")
    p.have(
        "h_body: "
        + _IS_PR_DEF_BODY.format(n="course_rec_base_def_axiom_at g h")
    ).by_disj("h_ex")
    p.thus("is_pr_def (course_rec_base_def_axiom_at g h)").by_unfold(
        "h_body", IS_PR_DEF_DEF
    )


@proof
def IS_PR_DEF_HOLDS_COURSE_REC_STEP(p):
    """|- !g h a b. is_pr_sym g /\\ is_pr_sym h
            ==> is_pr_def (course_rec_step_def_axiom_at g h a b).

    4-binder existential leaf (g, h, a, b). The is_pr_sym hypotheses
    apply only to g, h (the symbol slots); a, b are unconstrained Pair_ord
    components.
    """
    from tactics import REFL
    p.goal(
        "!g h a b. is_pr_sym g /\\ is_pr_sym h "
        "==> is_pr_def (course_rec_step_def_axiom_at g h a b)",
        types={"g": nat0_ty, "h": nat0_ty,
               "a": nat0_ty, "b": nat0_ty},
    )
    p.fix("g h a b")
    p.assume("(h_g, h_h): is_pr_sym g /\\ is_pr_sym h")
    p.have(
        "h_refl: course_rec_step_def_axiom_at g h a b "
        "      = course_rec_step_def_axiom_at g h a b"
    ).by_thm(REFL(p._parse("course_rec_step_def_axiom_at g h a b")))
    p.have(
        "h_ex: ?gg hh aa bb. course_rec_step_def_axiom_at g h a b "
        "      = course_rec_step_def_axiom_at gg hh aa bb "
        "      /\\ is_pr_sym gg /\\ is_pr_sym hh"
    ).by_exists(["g", "h", "a", "b"], "h_refl", "h_g", "h_h")
    p.have(
        "h_body: "
        + _IS_PR_DEF_BODY.format(n="course_rec_step_def_axiom_at g h a b")
    ).by_disj("h_ex")
    p.thus("is_pr_def (course_rec_step_def_axiom_at g h a b)").by_unfold(
        "h_body", IS_PR_DEF_DEF
    )


@proof
def IS_PR_DEF_HOLDS_CONST(p):
    """|- !c. is_pr_def (const_def_axiom_at c).

    Unconditional: the const axiom is parametric on any c with no
    side condition. Single-binder existential leaf (?cc. ... = ...).
    """
    from tactics import REFL
    p.goal(
        "!c. is_pr_def (const_def_axiom_at c)",
        types={"c": nat0_ty},
    )
    p.fix("c")
    p.have(
        "h_refl: const_def_axiom_at c = const_def_axiom_at c"
    ).by_thm(REFL(p._parse("const_def_axiom_at c")))
    p.have(
        "h_ex: ?cc. const_def_axiom_at c = const_def_axiom_at cc"
    ).by_exists(["c"], "h_refl")
    p.have(
        "h_body: " + _IS_PR_DEF_BODY.format(n="const_def_axiom_at c")
    ).by_disj("h_ex")
    p.thus("is_pr_def (const_def_axiom_at c)").by_unfold(
        "h_body", IS_PR_DEF_DEF
    )


@proof
def IS_PR_DEF_HOLDS_PAIR_LEFT(p):
    """|- !a b. is_pr_def (pair_left_def_axiom_at a b).

    Unconditional 2-binder existential (no side condition on a, b).
    Same proof shape as IS_PR_DEF_HOLDS_REC_BASE minus the is_pr_sym
    hypotheses.
    """
    from tactics import REFL
    p.goal(
        "!a b. is_pr_def (pair_left_def_axiom_at a b)",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.fix("a b")
    p.have(
        "h_refl: pair_left_def_axiom_at a b = pair_left_def_axiom_at a b"
    ).by_thm(REFL(p._parse("pair_left_def_axiom_at a b")))
    p.have(
        "h_ex: ?aa bb. pair_left_def_axiom_at a b = pair_left_def_axiom_at aa bb"
    ).by_exists(["a", "b"], "h_refl")
    p.have(
        "h_body: " + _IS_PR_DEF_BODY.format(n="pair_left_def_axiom_at a b")
    ).by_disj("h_ex")
    p.thus("is_pr_def (pair_left_def_axiom_at a b)").by_unfold(
        "h_body", IS_PR_DEF_DEF
    )


@proof
def IS_PR_DEF_HOLDS_PAIR_RIGHT(p):
    """|- !a b. is_pr_def (pair_right_def_axiom_at a b)."""
    from tactics import REFL
    p.goal(
        "!a b. is_pr_def (pair_right_def_axiom_at a b)",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.fix("a b")
    p.have(
        "h_refl: pair_right_def_axiom_at a b = pair_right_def_axiom_at a b"
    ).by_thm(REFL(p._parse("pair_right_def_axiom_at a b")))
    p.have(
        "h_ex: ?aa bb. pair_right_def_axiom_at a b = pair_right_def_axiom_at aa bb"
    ).by_exists(["a", "b"], "h_refl")
    p.have(
        "h_body: " + _IS_PR_DEF_BODY.format(n="pair_right_def_axiom_at a b")
    ).by_disj("h_ex")
    p.thus("is_pr_def (pair_right_def_axiom_at a b)").by_unfold(
        "h_body", IS_PR_DEF_DEF
    )


@proof
def IS_PR_DEF_HOLDS_PAIR_ORD(p):
    """|- !a b. is_pr_def (pair_ord_def_axiom_at a b)."""
    from tactics import REFL
    p.goal(
        "!a b. is_pr_def (pair_ord_def_axiom_at a b)",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.fix("a b")
    p.have(
        "h_refl: pair_ord_def_axiom_at a b = pair_ord_def_axiom_at a b"
    ).by_thm(REFL(p._parse("pair_ord_def_axiom_at a b")))
    p.have(
        "h_ex: ?aa bb. pair_ord_def_axiom_at a b = pair_ord_def_axiom_at aa bb"
    ).by_exists(["a", "b"], "h_refl")
    p.have(
        "h_body: " + _IS_PR_DEF_BODY.format(n="pair_ord_def_axiom_at a b")
    ).by_disj("h_ex")
    p.thus("is_pr_def (pair_ord_def_axiom_at a b)").by_unfold(
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
    f"\\g:nat0. \\hs:nat0. Pair_ord ({suc_chain(5)}) (Pair_ord g hs)",
)
comp_sym = mk_const("comp_sym", [])


# PRST_COMP_DEF is a Prov_PRST claim about comp_sym; it lives in
# prst_proof to avoid the forward reference.


@proof
def IS_PR_SYM_COMP(p):
    """|- !g hs. is_pr_sym (comp_sym g hs).

    `comp_sym g hs = Pair_ord 5 (Pair_ord g hs)`, which falls under the
    broad tag-5 branch already used by const_sym. Closure checks for g
    and hs are proof-system obligations, not syntactic registry obligations.
    """
    p.goal("!g hs. is_pr_sym (comp_sym g hs)", types={"g": nat0_ty, "hs": nat0_ty})
    p.fix("g hs")
    comp_eq_th = p.unfold(comp_sym_def, "g", "hs")
    p.have(
        f"comp_eq: comp_sym g hs = Pair_ord ({suc_chain(5)}) (Pair_ord g hs)"
    ).by_thm(comp_eq_th)
    p.have(
        f"h_ex: ?c. comp_sym g hs = Pair_ord ({suc_chain(5)}) c"
    ).by_exists(["Pair_ord g hs"], "comp_eq")
    p.have(
        "h_body: " + _IS_PR_SYM_BODY.format(sym="comp_sym g hs").replace(
            "?g h.", "?gg hh."
        ).replace("Pair_ord g h", "Pair_ord gg hh")
    ).by_disj("h_ex")
    p.thus("is_pr_sym (comp_sym g hs)").by_unfold("h_body", IS_PR_SYM_DEF)


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
    f"\\f:nat0. Pair_ord ({suc_chain(6)}) f",
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
    p.have(f"h_pair: nat0_lt g (Pair_ord ({suc_chain(6)}) g)").by(
        NAT0_LT_PAIR_ORD_R, suc_chain(6), "g"
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
        f"h_eq: mu_sym f = Pair_ord ({suc_chain(6)}) f"
    ).by_thm(mu_at_f)
    p.have(
        f"h_ex: ?gg. mu_sym f = Pair_ord ({suc_chain(6)}) gg "
        f"        /\\ is_partial_pr_sym gg"
    ).by_exists(["f"], "h_eq", "h_part")
    # Disjunction body of _IS_PARTIAL_PR_SYM_F at n := mu_sym f.
    p.have(
        f"h_body: is_pr_sym (mu_sym f) "
        f"        \\/ (?gg. mu_sym f = Pair_ord ({suc_chain(6)}) gg "
        f"                  /\\ is_partial_pr_sym gg)"
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
# ``is_pr_axiom`` (= is_pr_def_instance \/ is_pr_refl \/ is_logical_axiom)
# and ``is_mp``.
# All primitive recursive. Total: ~50 base-layer symbols composed.
#
# The full implementation is ~600 lines; PR symbols are first-class
# terms, so there are no trace sets and no functionality proofs.
# ---------------------------------------------------------------------------


# numeral_pr := REC zero_sym (\i,s,r,_vec. Adj_pt r r)
#            =  rec_sym zero_sym (comp_sym adj_sym (proj 2 4) (proj 2 4))
# 4-ary step (i, s, r, y_vec), zero-ary y_vec collapses to no
# additional slots; proj 2 4 picks ``r`` (the 3rd of 4 args).
numeral_pr_def = define(
    "numeral_pr",
    parse_type("nat0"),
    rec(zero_sym, comp(adj_sym, proj(2, 4), proj(2, 4))),
)
numeral_pr = mk_const("numeral_pr", [])


# ---------------------------------------------------------------------------
# substitute_pr -- structural recursion on the formula tree via course_rec.
#
# Design:
#   substitute_pr := comp_sym (course_rec g_subst h_subst) [F_proj, y_packer]
# where:
#   F_proj   = proj 0 3                              -- extract F
#   y_packer = comp_sym pair_ord_sym [proj 1 3, proj 2 3]
#              -- pack (t, v) into Pair_ord t v as the single y_vec slot
#
# g_subst (base case, course_rec input = 0 = Empty_pt): returns
# Empty_pt = 0. Implemented as const_sym 0.
#
# h_subst (step case, course_rec input = Pair_ord a b): dispatches on
# tag a via a nested if_in_sym chain across the formula constructors:
#   a = 2  (Var_pt v):   if b ∈ {pair_right y_vec} then pair_left y_vec
#                        else Pair_ord 2 b   (= Var_pt b)
#   a = 5  (Eq_pf):      Pair_ord 5 rec_right
#   a = 6  (Not_pf):     Pair_ord 6 rec_right
#   a = 7  (Imp_pf):     Pair_ord 7 rec_right
#   a = 10 (In_pa):      Pair_ord 10 rec_right
#   a = 11 (App_pt):     Pair_ord 11 (Pair_ord (pair_left b) (pair_right rec_right))
#                        -- non-uniform: keep fn unchanged, recurse only on args.
#   a = 12 (Tup_pt):     Pair_ord 12 rec_right
#   else:                Pair_ord rec_left rec_right
#                        -- intermediate Pair_ord layer (binary constructor's
#                        inner-pair-of-children level).
#
# y_vec carries Pair_ord t v throughout (packed by the outer comp_sym).
# h_subst receives 5 args: (a, b, rec_left, rec_right, y_vec); extracts
# via proj 0..4 of 5.
# ---------------------------------------------------------------------------


def _h_subst_const(value_term):
    """PR symbol whose value at h_subst's 5-arg input is constant
    ``value_term``. Wraps const_sym in a comp_sym + 1-arg projection so
    its defining axiom (at 1-arg input) reduces at h_subst's 5-arg call
    site."""
    return comp(mk_app(const_sym, value_term), proj(0, 5))


def _h_subst_if_eq(tag_val, then_pr, else_pr):
    """Dispatch on (a == tag_val) where a is h_subst's first arg.
    Uses if_in_sym test against the singleton set {tag_val} =
    Adj_pt (nat tag_val) Empty_pt."""
    singleton = _adj_pt_b(nat(tag_val), Empty_pt)
    return comp(if_in_sym,
                proj(0, 5),               # test: a
                _h_subst_const(singleton),  # t_val: {tag_val}
                then_pr,
                else_pr)


# Default case (intermediate Pair_ord, no constructor-tag dispatch
# matched): Pair_ord rec_left rec_right.
_h_subst_default = comp(pair_ord_sym, proj(2, 5), proj(3, 5))

# Tup_pt case (a = 12): Pair_ord 12 rec_right.
_h_subst_tup = comp(pair_ord_sym, _h_subst_const(nat(12)), proj(3, 5))

# App_pt case (a = 11): Pair_ord 11 (Pair_ord (pair_left b) (pair_right rec_right)).
_h_subst_app = comp(
    pair_ord_sym,
    _h_subst_const(nat(11)),
    comp(pair_ord_sym,
         comp(pair_left_sym, proj(1, 5)),
         comp(pair_right_sym, proj(3, 5))),
)

# In_pa case (a = 10): Pair_ord 10 rec_right.
_h_subst_in = comp(pair_ord_sym, _h_subst_const(nat(10)), proj(3, 5))

# Imp_pf case (a = 7): Pair_ord 7 rec_right.
_h_subst_imp = comp(pair_ord_sym, _h_subst_const(nat(7)), proj(3, 5))

# Not_pf case (a = 6): Pair_ord 6 rec_right.
_h_subst_not = comp(pair_ord_sym, _h_subst_const(nat(6)), proj(3, 5))

# Eq_pf case (a = 5): Pair_ord 5 rec_right.
_h_subst_eq = comp(pair_ord_sym, _h_subst_const(nat(5)), proj(3, 5))

# Var_pt case (a = 2): if b ∈ {pair_right y_vec} then pair_left y_vec
# else Pair_ord 2 b. The singleton {pair_right y_vec} is built at PR
# level via Adj_pt with adj_sym applied to (pair_right y_vec, Empty_pt).
_h_subst_var = comp(
    if_in_sym,
    proj(1, 5),                                          # b
    comp(adj_sym,                                        # {pair_right y_vec}
         comp(pair_right_sym, proj(4, 5)),
         _h_subst_const(Empty_pt)),
    comp(pair_left_sym, proj(4, 5)),                     # pair_left y_vec (= t)
    comp(pair_ord_sym, _h_subst_const(nat(2)), proj(1, 5)),  # Pair_ord 2 b
)

# Nested if_in dispatch (Var → Eq → Not → Imp → In → App → Tup → default).
_h_subst_body = _h_subst_if_eq(2,  _h_subst_var,
                _h_subst_if_eq(5,  _h_subst_eq,
                _h_subst_if_eq(6,  _h_subst_not,
                _h_subst_if_eq(7,  _h_subst_imp,
                _h_subst_if_eq(10, _h_subst_in,
                _h_subst_if_eq(11, _h_subst_app,
                _h_subst_if_eq(12, _h_subst_tup,
                               _h_subst_default)))))))

G_SUBST_DEF = define("g_subst", parse_type("nat0"),
                     mk_app(const_sym, nat(0)))
g_subst = mk_const("g_subst", [])

H_SUBST_DEF = define("h_subst", parse_type("nat0"), _h_subst_body)
h_subst = mk_const("h_subst", [])

# substitute_pr := course_rec g_subst h_subst applied via outer comp_sym
# that wires substitute_pr's 3-arg input (F, t, v) into course_rec's
# 2-arg input (F, Pair_ord t v).
substitute_pr_def = define(
    "substitute_pr",
    parse_type("nat0"),
    comp(
        mk_app(mk_app(course_rec_sym, g_subst), h_subst),
        proj(0, 3),                                       # F
        comp(pair_ord_sym, proj(1, 3), proj(2, 3)),       # Pair_ord t v
    ),
)
substitute_pr = mk_const("substitute_pr", [])


# diag_pr n := substitute_pr (n, numeral_pr n, var_x).
# Compositional shape: comp_sym substitute_pr applied to three 1-ary
# argument-shapers, each fed the original n:
#   * proj 0 1                       -- yields n
#   * comp numeral_pr (proj 0 1)     -- yields numeral n
#   * const_sym (Var_pt var_x)       -- yields var_x (constant function)
# The const slot is now closed via the new const_sym primitive: its
# defining axiom App_pt (const_sym c) (Tup_pt _ Empty_pt) = c lets the
# argument vector evaluate to var_x regardless of the carried n.
# substitute_pr's third arg is the variable INDEX (nat0), not a Var_pt
# term. var_x is defined in hf_proof as `Var_t 0`; here we use the
# encoded form directly to avoid a hf_proof import dependency.
diag_pr_def = define(
    "diag_pr",
    parse_type("nat0"),
    comp(
        substitute_pr,
        proj(0, 1),
        comp(numeral_pr, proj(0, 1)),
        mk_app(const_sym, var_t(0)),  # const (Var_t 0) = const var_x
    ),
)
diag_pr = mk_const("diag_pr", [])


# Proof_PRST_pr -- the list-of-formulas proof checker as a PR symbol.
#
# This is the actual checker shape, replacing the old sentinel
# ``proj 1 2``.  The definition is deliberately decomposed into named
# helper symbols so the later correctness proof can unfold one layer at
# a time:
#
#   Proof_PRST_pr(p, n)
#     = is_tup(p) /\ head(p) = n /\ valid_proof_list(p)
#
#   valid_proof_list(Empty_pt) = T
#   valid_proof_list(Tup_pt h t)
#     = valid_proof_list(t) /\ valid_step(h, t)
#
#   valid_step(h, t)
#     = is_pr_axiom_pr(h)
#       \/ exists f in t. mem_t(Imp_pf f h, t)
#
# The critical MP point is membership search in the earlier list t.  We
# never ask the single-conclusion predicate for "tail proves f" and
# "tail proves f -> h"; that was the broken shape in _Proof_PRST_F.
#
# The only leaf intentionally left as a separate recogniser symbol is
# ``is_pr_axiom_pr``.  Expanding that symbol into
# is_pr_def_instance_pr \/ is_pr_refl_pr \/ is_logical_axiom_pr is the next
# schema-recogniser task, not part of the proof-list recursion itself.


def _const_at(value_term, arity):
    """PR symbol that ignores an ``arity``-tuple and returns value_term."""
    return comp(mk_app(const_sym, value_term), proj(0, arity))


def _singleton_at(value_pr, arity):
    """PR symbol returning the singleton set ``{value_pr(args)}``."""
    return comp(adj_sym, value_pr, _const_at(Empty_pt, arity))


def _if_eq_literal_at(tag_val, arity, test_pr, then_pr, else_pr):
    """Branch on ``test_pr(args) = tag_val`` using if_in over a singleton."""
    return comp(
        if_in_sym,
        test_pr,
        _singleton_at(_const_at(nat(tag_val), arity), arity),
        then_pr,
        else_pr,
    )


eq_nat_pr_def = define(
    "eq_nat_pr",
    parse_type("nat0"),
    comp(
        if_in_sym,
        proj(0, 2),
        _singleton_at(proj(1, 2), 2),
        _const_at(T_pt, 2),
        _const_at(F_pt, 2),
    ),
)
eq_nat_pr = mk_const("eq_nat_pr", [])


or_bool_pr_def = define(
    "or_bool_pr",
    parse_type("nat0"),
    comp(
        if_in_sym,
        proj(0, 2),
        _singleton_at(_const_at(T_pt, 2), 2),
        _const_at(T_pt, 2),
        proj(1, 2),
    ),
)
or_bool_pr = mk_const("or_bool_pr", [])


and_bool_pr_def = define(
    "and_bool_pr",
    parse_type("nat0"),
    comp(
        if_in_sym,
        proj(0, 2),
        _singleton_at(_const_at(T_pt, 2), 2),
        proj(1, 2),
        _const_at(F_pt, 2),
    ),
)
and_bool_pr = mk_const("and_bool_pr", [])


# Tup_pt p = Pair_ord 12 (Pair_ord h t).  The destructors below assume
# the Tup_pt shape; callers guard with is_tup_pr when that matters.
tup_payload_pr_def = define(
    "tup_payload_pr",
    parse_type("nat0"),
    comp(pair_right_sym, proj(0, 1)),
)
tup_payload_pr = mk_const("tup_payload_pr", [])


tup_head_pr_def = define(
    "tup_head_pr",
    parse_type("nat0"),
    comp(pair_left_sym, tup_payload_pr),
)
tup_head_pr = mk_const("tup_head_pr", [])


tup_tail_pr_def = define(
    "tup_tail_pr",
    parse_type("nat0"),
    comp(pair_right_sym, tup_payload_pr),
)
tup_tail_pr = mk_const("tup_tail_pr", [])


is_tup_pr_def = define(
    "is_tup_pr",
    parse_type("nat0"),
    comp(eq_nat_pr, comp(pair_left_sym, proj(0, 1)), _const_at(nat(12), 1)),
)
is_tup_pr = mk_const("is_tup_pr", [])


# Build the encoded PRST implication formula Imp_pf f h =
# Pair_ord 7 (Pair_ord f h).
imp_code_pr_def = define(
    "imp_code_pr",
    parse_type("nat0"),
    comp(
        pair_ord_sym,
        _const_at(nat(7), 2),
        comp(pair_ord_sym, proj(0, 2), proj(1, 2)),
    ),
)
imp_code_pr = mk_const("imp_code_pr", [])


# PR-side axiom recogniser skeleton.  This mirrors the HOL-side
# is_pr_axiom shape from prst_proof:
#
#   is_pr_axiom
#     = is_pr_def_instance \/ is_pr_refl \/ is_logical_axiom
#
# The large schema-recogniser leaves are intentionally separate PR symbols so
# Proof_PRST_pr has the right shape now, while the remaining bounded
# recogniser work is localized.
def _or_many_pr(items):
    """Right-associated boolean OR over same-arity PR predicate symbols."""
    out = items[-1]
    for item in reversed(items[:-1]):
        out = comp(or_bool_pr, item, out)
    return out


def _and_many_pr(items):
    """Right-associated boolean AND over same-arity PR predicate symbols."""
    out = items[-1]
    for item in reversed(items[:-1]):
        out = comp(and_bool_pr, item, out)
    return out


def _eq_const_at(value_term, arity):
    return comp(eq_nat_pr, proj(0, arity), _const_at(value_term, arity))


def _tag_eq_at(tag_val, arity, term_pr):
    return comp(eq_nat_pr, comp(pair_left_sym, term_pr), _const_at(nat(tag_val), arity))


def _payload_at(term_pr):
    return comp(pair_right_sym, term_pr)


def _pair_left_at(term_pr):
    return comp(pair_left_sym, term_pr)


def _pair_right_at(term_pr):
    return comp(pair_right_sym, term_pr)


def _binary_left_at(term_pr):
    return _pair_left_at(_payload_at(term_pr))


def _binary_right_at(term_pr):
    return _pair_right_at(_payload_at(term_pr))


def _imp_left_at(term_pr):
    return _binary_left_at(term_pr)


def _imp_right_at(term_pr):
    return _binary_right_at(term_pr)


def _not_payload_at(term_pr):
    return _payload_at(term_pr)


def _eq_pf_left_at(term_pr):
    return _binary_left_at(term_pr)


def _eq_pf_right_at(term_pr):
    return _binary_right_at(term_pr)


def _in_pa_left_at(term_pr):
    return _binary_left_at(term_pr)


def _in_pa_right_at(term_pr):
    return _binary_right_at(term_pr)


def _app_fn_at(term_pr):
    return _binary_left_at(term_pr)


def _app_args_at(term_pr):
    return _binary_right_at(term_pr)


def _tup_head_at(term_pr):
    return _binary_left_at(term_pr)


def _tup_tail_at(term_pr):
    return _binary_right_at(term_pr)


def _eq_at(left_pr, right_pr):
    return comp(eq_nat_pr, left_pr, right_pr)


def _is_empty_at(term_pr):
    return _eq_at(term_pr, _const_at(Empty_pt, 1))


def _slot_const_at(slot, arity=1):
    return _const_at(var_t(slot), arity)


def _slot_expected_at(formal_slot, replaced_slot, replacement_pr):
    if formal_slot == replaced_slot:
        return replacement_pr
    return _slot_const_at(formal_slot)


def _slot_consistency_checks(candidates, formal_slots, replaced_slot):
    replacement = next(
        candidate
        for candidate, slot in zip(candidates, formal_slots)
        if slot == replaced_slot
    )
    return [
        _eq_at(
            candidate,
            _slot_expected_at(slot, replaced_slot, replacement),
        )
        for candidate, slot in zip(candidates, formal_slots)
    ]


def _if_in_schema_instance_matcher(negated_antecedent=False, rhs_slot=2):
    """Recognizer for one substituted ``if_in`` defining-equation schema."""
    n_pr = proj(0, 1)
    antecedent_pr = _imp_left_at(n_pr)
    in_pr = _not_payload_at(antecedent_pr) if negated_antecedent else antecedent_pr
    eq_pr = _imp_right_at(n_pr)
    app_pr = _eq_pf_left_at(eq_pr)
    args0_pr = _app_args_at(app_pr)
    args1_pr = _tup_tail_at(args0_pr)
    args2_pr = _tup_tail_at(args1_pr)
    args3_pr = _tup_tail_at(args2_pr)
    args4_pr = _tup_tail_at(args3_pr)

    candidates = [
        _in_pa_left_at(in_pr),
        _in_pa_right_at(in_pr),
        _tup_head_at(args0_pr),
        _tup_head_at(args1_pr),
        _tup_head_at(args2_pr),
        _tup_head_at(args3_pr),
        _eq_pf_right_at(eq_pr),
    ]
    formal_slots = [0, 1, 0, 1, 2, 3, rhs_slot]

    shape_checks = [
        _tag_eq_at(7, 1, n_pr),
        _tag_eq_at(10, 1, in_pr),
        _tag_eq_at(5, 1, eq_pr),
        _tag_eq_at(11, 1, app_pr),
        _eq_at(_app_fn_at(app_pr), _const_at(if_in_sym, 1)),
        _tag_eq_at(12, 1, args0_pr),
        _tag_eq_at(12, 1, args1_pr),
        _tag_eq_at(12, 1, args2_pr),
        _tag_eq_at(12, 1, args3_pr),
        _is_empty_at(args4_pr),
    ]
    if negated_antecedent:
        shape_checks.insert(1, _tag_eq_at(6, 1, antecedent_pr))
    return _or_many_pr(
        [
            _and_many_pr(
                shape_checks
                + _slot_consistency_checks(candidates, formal_slots, replaced_slot)
            )
            for replaced_slot in range(4)
        ]
    )


is_zero_def_instance_pr_def = define(
    "is_zero_def_instance_pr",
    parse_type("nat0"),
    _eq_const_at(zero_def_axiom, 1),
)
is_zero_def_instance_pr = mk_const("is_zero_def_instance_pr", [])


is_if_in_true_def_instance_pr_def = define(
    "is_if_in_true_def_instance_pr",
    parse_type("nat0"),
    _if_in_schema_instance_matcher(negated_antecedent=False, rhs_slot=2),
)
is_if_in_true_def_instance_pr = mk_const("is_if_in_true_def_instance_pr", [])


is_if_in_false_def_instance_pr_def = define(
    "is_if_in_false_def_instance_pr",
    parse_type("nat0"),
    _if_in_schema_instance_matcher(negated_antecedent=True, rhs_slot=3),
)
is_if_in_false_def_instance_pr = mk_const("is_if_in_false_def_instance_pr", [])


# PR-def-instance recogniser slice.  Substituted instances are matched by
# schema-specific PR predicates: each matcher reads the replaced formal slot
# from the candidate and checks every repeated occurrence for consistency.
# The remaining PR-def axiom families still need corresponding matcher leaves.
is_pr_def_instance_pr_def = define(
    "is_pr_def_instance_pr",
    parse_type("nat0"),
    _or_many_pr([
        is_zero_def_instance_pr,
        is_if_in_true_def_instance_pr,
        is_if_in_false_def_instance_pr,
    ]),
)
is_pr_def_instance_pr = mk_const("is_pr_def_instance_pr", [])


# PR-symbol-shape recogniser used by is_pterm_pr's App_pt branch.  This is
# intentionally syntactic: it accepts the registered literal symbols and the
# parametric PR-symbol tag families, including the mu tag used by partial PR
# symbols. Closure correctness remains with the HOL-side registry.
is_partial_pr_sym_pr_def = define(
    "is_partial_pr_sym_pr",
    parse_type("nat0"),
    _or_many_pr([
        _eq_const_at(nat(0), 1),
        _eq_const_at(nat(1), 1),
        _eq_const_at(nat(3), 1),
        _eq_const_at(nat(8), 1),
        _eq_const_at(nat(9), 1),
        _eq_const_at(nat(10), 1),
        _tag_eq_at(2, 1, proj(0, 1)),
        _tag_eq_at(4, 1, proj(0, 1)),
        _tag_eq_at(5, 1, proj(0, 1)),
        _tag_eq_at(6, 1, proj(0, 1)),
        _tag_eq_at(7, 1, proj(0, 1)),
    ]),
)
is_partial_pr_sym_pr = mk_const("is_partial_pr_sym_pr", [])


# is_pterm_pr is computed by a Pair_ord course recursion that returns an
# auxiliary pair Pair_ord(is_term_bool, child_bool_pair).  Constructor nodes
# expose is_term_bool; intermediate payload pairs expose their child booleans
# so App_pt can check only its argument tuple while treating the function id
# through is_partial_pr_sym_pr.
_is_pterm_aux_true = _pair_ord_b(T_pt, Empty_pt)
g_is_pterm_aux_pr_def = define(
    "g_is_pterm_aux_pr",
    parse_type("nat0"),
    mk_app(const_sym, _is_pterm_aux_true),
)
g_is_pterm_aux_pr = mk_const("g_is_pterm_aux_pr", [])

_h_is_pterm_rec_left_bool = comp(pair_left_sym, proj(2, 5))
_h_is_pterm_rec_right_bool = comp(pair_left_sym, proj(3, 5))
_h_is_pterm_child_bools = comp(
    pair_ord_sym,
    _h_is_pterm_rec_left_bool,
    _h_is_pterm_rec_right_bool,
)
_h_is_pterm_default = comp(
    pair_ord_sym,
    _const_at(F_pt, 5),
    _h_is_pterm_child_bools,
)
_h_is_pterm_var = comp(
    pair_ord_sym,
    _const_at(T_pt, 5),
    _const_at(Empty_pt, 5),
)
_h_is_pterm_payload_bools = comp(pair_right_sym, proj(3, 5))
_h_is_pterm_payload_left_bool = comp(pair_left_sym, _h_is_pterm_payload_bools)
_h_is_pterm_payload_right_bool = comp(pair_right_sym, _h_is_pterm_payload_bools)
_h_is_pterm_tup_bool = comp(
    and_bool_pr,
    _h_is_pterm_payload_left_bool,
    _h_is_pterm_payload_right_bool,
)
_h_is_pterm_tup = comp(
    pair_ord_sym,
    _h_is_pterm_tup_bool,
    _const_at(Empty_pt, 5),
)
_h_is_pterm_app_bool = comp(
    and_bool_pr,
    comp(is_partial_pr_sym_pr, comp(pair_left_sym, proj(1, 5))),
    _h_is_pterm_payload_right_bool,
)
_h_is_pterm_app = comp(
    pair_ord_sym,
    _h_is_pterm_app_bool,
    _const_at(Empty_pt, 5),
)
_h_is_pterm_aux_body = _if_eq_literal_at(
    2, 5, proj(0, 5), _h_is_pterm_var,
    _if_eq_literal_at(
        11, 5, proj(0, 5), _h_is_pterm_app,
        _if_eq_literal_at(12, 5, proj(0, 5), _h_is_pterm_tup, _h_is_pterm_default),
    ),
)
h_is_pterm_aux_pr_def = define(
    "h_is_pterm_aux_pr",
    parse_type("nat0"),
    _h_is_pterm_aux_body,
)
h_is_pterm_aux_pr = mk_const("h_is_pterm_aux_pr", [])

is_pterm_pr_def = define(
    "is_pterm_pr",
    parse_type("nat0"),
    comp(
        pair_left_sym,
        comp(
            mk_app(mk_app(course_rec_sym, g_is_pterm_aux_pr), h_is_pterm_aux_pr),
            proj(0, 1),
            _const_at(nat(0), 1),
        ),
    ),
)
is_pterm_pr = mk_const("is_pterm_pr", [])


# Propositional logical axiom slice over PRST formula constructors:
#   K: A -> (B -> A)
#   S: (A -> (B -> C)) -> ((A -> B) -> (A -> C))
#   N: (~B -> ~A) -> (A -> B)
# Quantifier and substitution schemas are left out of this PR spike because
# PRST has no object-level Forall_pf and substitution is handled through
# is_pr_def_instance.
_n_pr = proj(0, 1)
_n_is_imp_pr = _tag_eq_at(7, 1, _n_pr)

_k_A_pr = _imp_left_at(_n_pr)
_k_R_pr = _imp_right_at(_n_pr)
_k_pr = _and_many_pr([
    _n_is_imp_pr,
    _tag_eq_at(7, 1, _k_R_pr),
    comp(eq_nat_pr, _k_A_pr, _imp_right_at(_k_R_pr)),
])

_s_L_pr = _imp_left_at(_n_pr)
_s_R_pr = _imp_right_at(_n_pr)
_s_A_pr = _imp_left_at(_s_L_pr)
_s_L2_pr = _imp_right_at(_s_L_pr)
_s_B_pr = _imp_left_at(_s_L2_pr)
_s_C_pr = _imp_right_at(_s_L2_pr)
_s_R1_pr = _imp_left_at(_s_R_pr)
_s_R2_pr = _imp_right_at(_s_R_pr)
_s_pr = _and_many_pr([
    _n_is_imp_pr,
    _tag_eq_at(7, 1, _s_L_pr),
    _tag_eq_at(7, 1, _s_L2_pr),
    _tag_eq_at(7, 1, _s_R_pr),
    _tag_eq_at(7, 1, _s_R1_pr),
    _tag_eq_at(7, 1, _s_R2_pr),
    comp(eq_nat_pr, _s_A_pr, _imp_left_at(_s_R1_pr)),
    comp(eq_nat_pr, _s_B_pr, _imp_right_at(_s_R1_pr)),
    comp(eq_nat_pr, _s_A_pr, _imp_left_at(_s_R2_pr)),
    comp(eq_nat_pr, _s_C_pr, _imp_right_at(_s_R2_pr)),
])

_n_L_pr = _imp_left_at(_n_pr)
_n_R_pr = _imp_right_at(_n_pr)
_n_not_B_pr = _imp_left_at(_n_L_pr)
_n_not_A_pr = _imp_right_at(_n_L_pr)
_n_A_pr = _imp_left_at(_n_R_pr)
_n_B_pr = _imp_right_at(_n_R_pr)
_n_axiom_pr = _and_many_pr([
    _n_is_imp_pr,
    _tag_eq_at(7, 1, _n_L_pr),
    _tag_eq_at(7, 1, _n_R_pr),
    _tag_eq_at(6, 1, _n_not_B_pr),
    _tag_eq_at(6, 1, _n_not_A_pr),
    comp(eq_nat_pr, _not_payload_at(_n_not_B_pr), _n_B_pr),
    comp(eq_nat_pr, _not_payload_at(_n_not_A_pr), _n_A_pr),
])

is_logical_axiom_pr_def = define(
    "is_logical_axiom_pr",
    parse_type("nat0"),
    _or_many_pr([_k_pr, _s_pr, _n_axiom_pr]),
)
is_logical_axiom_pr = mk_const("is_logical_axiom_pr", [])


eq_pf_payload_pr_def = define(
    "eq_pf_payload_pr",
    parse_type("nat0"),
    comp(pair_right_sym, proj(0, 1)),
)
eq_pf_payload_pr = mk_const("eq_pf_payload_pr", [])


eq_pf_left_pr_def = define(
    "eq_pf_left_pr",
    parse_type("nat0"),
    comp(pair_left_sym, eq_pf_payload_pr),
)
eq_pf_left_pr = mk_const("eq_pf_left_pr", [])


eq_pf_right_pr_def = define(
    "eq_pf_right_pr",
    parse_type("nat0"),
    comp(pair_right_sym, eq_pf_payload_pr),
)
eq_pf_right_pr = mk_const("eq_pf_right_pr", [])


is_eq_pf_tag_pr_def = define(
    "is_eq_pf_tag_pr",
    parse_type("nat0"),
    comp(eq_nat_pr, comp(pair_left_sym, proj(0, 1)), _const_at(nat(5), 1)),
)
is_eq_pf_tag_pr = mk_const("is_eq_pf_tag_pr", [])


is_eq_pf_refl_shape_pr_def = define(
    "is_eq_pf_refl_shape_pr",
    parse_type("nat0"),
    comp(
        and_bool_pr,
        is_eq_pf_tag_pr,
        comp(eq_nat_pr, eq_pf_left_pr, eq_pf_right_pr),
    ),
)
is_eq_pf_refl_shape_pr = mk_const("is_eq_pf_refl_shape_pr", [])


is_pr_refl_pr_def = define(
    "is_pr_refl_pr",
    parse_type("nat0"),
    comp(
        and_bool_pr,
        is_eq_pf_refl_shape_pr,
        comp(is_pterm_pr, eq_pf_left_pr),
    ),
)
is_pr_refl_pr = mk_const("is_pr_refl_pr", [])


is_pr_axiom_pr_def = define(
    "is_pr_axiom_pr",
    parse_type("nat0"),
    comp(
        or_bool_pr,
        is_pr_def_instance_pr,
        comp(or_bool_pr, is_pr_refl_pr, is_logical_axiom_pr),
    ),
)
is_pr_axiom_pr = mk_const("is_pr_axiom_pr", [])


# mem_t_pr(x, p): search a Tup_pt proof-list p for line x.
#
# Implemented by course_rec over raw Pair_ord.  At a real Tup_pt node
# Pair_ord 12 (Pair_ord h t), rec_right is the recursive result at the
# payload Pair_ord h t.  Non-Tup payload pairs forward their right
# recursion result, so rec_right at the Tup node is exactly mem_t(x,t).
g_mem_t_pr_def = define("g_mem_t_pr", parse_type("nat0"), mk_app(const_sym, F_pt))
g_mem_t_pr = mk_const("g_mem_t_pr", [])

_h_mem_t_then = comp(
    or_bool_pr,
    comp(eq_nat_pr, proj(4, 5), comp(pair_left_sym, proj(1, 5))),
    proj(3, 5),
)
h_mem_t_pr_def = define(
    "h_mem_t_pr",
    parse_type("nat0"),
    _if_eq_literal_at(12, 5, proj(0, 5), _h_mem_t_then, proj(3, 5)),
)
h_mem_t_pr = mk_const("h_mem_t_pr", [])

mem_t_pr_def = define(
    "mem_t_pr",
    parse_type("nat0"),
    comp(
        mk_app(mk_app(course_rec_sym, g_mem_t_pr), h_mem_t_pr),
        proj(1, 2),  # proof list p
        proj(0, 2),  # searched line x
    ),
)
mem_t_pr = mk_const("mem_t_pr", [])


# exists_mp_witness_pr(h, t): bounded MP search over earlier lines f in t.
# y_vec is Pair_ord h t, so every recursive step can test membership in
# the original earlier-list t, not merely the current rest.
g_exists_mp_pr_def = define(
    "g_exists_mp_pr",
    parse_type("nat0"),
    mk_app(const_sym, F_pt),
)
g_exists_mp_pr = mk_const("g_exists_mp_pr", [])

_exists_mp_candidate = comp(
    mem_t_pr,
    comp(
        imp_code_pr,
        comp(pair_left_sym, proj(1, 5)),   # f = head(payload)
        comp(pair_left_sym, proj(4, 5)),   # h = pair_left y_vec
    ),
    comp(pair_right_sym, proj(4, 5)),      # original t = pair_right y_vec
)
_h_exists_mp_then = comp(or_bool_pr, _exists_mp_candidate, proj(3, 5))
h_exists_mp_pr_def = define(
    "h_exists_mp_pr",
    parse_type("nat0"),
    _if_eq_literal_at(12, 5, proj(0, 5), _h_exists_mp_then, proj(3, 5)),
)
h_exists_mp_pr = mk_const("h_exists_mp_pr", [])

exists_mp_witness_pr_def = define(
    "exists_mp_witness_pr",
    parse_type("nat0"),
    comp(
        mk_app(mk_app(course_rec_sym, g_exists_mp_pr), h_exists_mp_pr),
        proj(1, 2),                                      # t
        comp(pair_ord_sym, proj(0, 2), proj(1, 2)),      # Pair_ord h t
    ),
)
exists_mp_witness_pr = mk_const("exists_mp_witness_pr", [])


valid_step_pr_def = define(
    "valid_step_pr",
    parse_type("nat0"),
    comp(
        or_bool_pr,
        comp(is_pr_axiom_pr, proj(0, 2)),
        comp(exists_mp_witness_pr, proj(0, 2), proj(1, 2)),
    ),
)
valid_step_pr = mk_const("valid_step_pr", [])


# valid_proof_list_pr(p): every line in the Tup_pt list is valid from
# its tail.
g_valid_proof_list_pr_def = define(
    "g_valid_proof_list_pr",
    parse_type("nat0"),
    mk_app(const_sym, T_pt),
)
g_valid_proof_list_pr = mk_const("g_valid_proof_list_pr", [])

_valid_step_at_payload = comp(
    valid_step_pr,
    comp(pair_left_sym, proj(1, 5)),    # h
    comp(pair_right_sym, proj(1, 5)),   # t
)
_h_valid_proof_list_then = comp(and_bool_pr, proj(3, 5), _valid_step_at_payload)
h_valid_proof_list_pr_def = define(
    "h_valid_proof_list_pr",
    parse_type("nat0"),
    _if_eq_literal_at(12, 5, proj(0, 5), _h_valid_proof_list_then, proj(3, 5)),
)
h_valid_proof_list_pr = mk_const("h_valid_proof_list_pr", [])

valid_proof_list_pr_def = define(
    "valid_proof_list_pr",
    parse_type("nat0"),
    comp(
        mk_app(mk_app(course_rec_sym, g_valid_proof_list_pr), h_valid_proof_list_pr),
        proj(0, 1),
        _const_at(nat(0), 1),
    ),
)
valid_proof_list_pr = mk_const("valid_proof_list_pr", [])


_proof_prst_head_matches = comp(eq_nat_pr, comp(tup_head_pr, proj(0, 2)), proj(1, 2))
_proof_prst_valid_tail = comp(
    and_bool_pr,
    _proof_prst_head_matches,
    comp(valid_proof_list_pr, proj(0, 2)),
)
_proof_prst_body = comp(
    and_bool_pr,
    comp(is_tup_pr, proj(0, 2)),
    _proof_prst_valid_tail,
)
Proof_PRST_pr_def = define(
    "Proof_PRST_pr",
    parse_type("nat0"),
    _proof_prst_body,
)
Proof_PRST_pr = mk_const("Proof_PRST_pr", [])


@proof
def IS_PR_SYM_PROOF_PRST_PR(p):
    """|- is_pr_sym Proof_PRST_pr."""
    from fusion import EQ_MP
    from tactics import AP_TERM, SPECL, SYM
    from basics import rand, rator

    p.goal("is_pr_sym Proof_PRST_pr")
    # _proof_prst_body is `comp_sym g hs`; peel g/hs from the kernel term
    # and specialise IS_PR_SYM_COMP at exactly that body.
    g_term = rand(rator(_proof_prst_body))
    hs_term = rand(_proof_prst_body)
    h_body = SPECL([g_term, hs_term], IS_PR_SYM_COMP)
    lift = AP_TERM(is_pr_sym, SYM(Proof_PRST_pr_def))
    p.thus("is_pr_sym Proof_PRST_pr").by_thm(EQ_MP(lift, h_body))


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
    print("Stage 2A (d) -- defining-equation godelnums (closed nat0s).")
    print("    ZERO_DEF_AXIOM_DEF        :", pp_thm(ZERO_DEF_AXIOM_DEF))
    print("    ADJ_PT_DEF                :", pp_thm(ADJ_PT_DEF))
    print("    IF_IN_TRUE_DEF_AXIOM_DEF  :", pp_thm(IF_IN_TRUE_DEF_AXIOM_DEF))
    print()
    print("Stage 2A (e) -- is_pr_def recogniser.")
    print("    IS_PR_DEF_DEF             :", pp_thm(IS_PR_DEF_DEF))
    print("    IS_PR_DEF_INSTANCE_DEF    :", pp_thm(IS_PR_DEF_INSTANCE_DEF))
    print("    IS_PR_DEF_HOLDS_ZERO      :", pp_thm(IS_PR_DEF_HOLDS_ZERO))
    print("    IS_PR_DEF_HOLDS_PROJ      :", pp_thm(IS_PR_DEF_HOLDS_PROJ))
    print("    IS_PR_DEF_HOLDS_REC_BASE  :", pp_thm(IS_PR_DEF_HOLDS_REC_BASE))
    print("    IS_PR_DEF_INSTANCE_SUBST  :", pp_thm(IS_PR_DEF_INSTANCE_SUBST))
    print()
    print("Stage 2A (h) -- PR-side axiom checker leaf.")
    print("    is_pr_def_instance_pr_def :", pp_thm(is_pr_def_instance_pr_def))
    print("    is_pr_refl_pr_def         :", pp_thm(is_pr_refl_pr_def))
    print("    is_logical_axiom_pr_def   :", pp_thm(is_logical_axiom_pr_def))
    print("    is_pr_axiom_pr_def        :", pp_thm(is_pr_axiom_pr_def))
    print()
    print("Prov_PRST claims about these axioms are one-line specialisations")
    print("of PROV_PRST_AX in prst_proof.")

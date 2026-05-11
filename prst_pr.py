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
#   * Adj       : 2-ary, primitive. ``App_pt adj_sym (cons_l a (cons_l
#                 b nil_l))`` IS the adjunction operation -- there is
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
from basics import mk_const
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof, define_with_at
from hf_proof import (
    nil_l,  # noqa: F401  -- parser alias for axiom bodies
    cons_l,  # noqa: F401  -- parser alias
)
from hf_syntax import (
    Var_t,  # noqa: F401  -- parser alias for free Var_t indices in axioms
)
from prst_syntax import (
    Empty_pt,  # noqa: F401  -- parser alias in PR-defining-equation bodies
    Var_pt,  # noqa: F401  -- parser alias
    Eq_pf,  # noqa: F401  -- parser alias
    Not_pf,  # noqa: F401  -- parser alias
    Imp_pf,  # noqa: F401  -- parser alias
    In_pa,  # noqa: F401  -- parser alias
    App_pt,
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


@proof
def IS_PR_SYM_ZERO(p):
    """|- is_pr_sym zero_sym. STUB."""
    p.goal("is_pr_sym zero_sym")
    p.sorry()


@proof
def IS_PR_SYM_ADJ(p):
    """|- is_pr_sym adj_sym. STUB."""
    p.goal("is_pr_sym adj_sym")
    p.sorry()


@proof
def IS_PR_SYM_PROJ(p):
    """|- !i n. nat0_lt i n ==> is_pr_sym (proj_sym i n). STUB."""
    p.goal(
        "!i n. nat0_lt i n ==> is_pr_sym (proj_sym i n)",
        types={"i": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


@proof
def IS_PR_SYM_IF_IN(p):
    """|- is_pr_sym if_in_sym. STUB."""
    p.goal("is_pr_sym if_in_sym")
    p.sorry()


@proof
def IS_PR_SYM_REC(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h ==> is_pr_sym (rec_sym g h). STUB."""
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h ==> is_pr_sym (rec_sym g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.sorry()


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
    "Eq_pf (App_pt zero_sym nil_l) Empty_pt",
)
zero_def_axiom = mk_const("zero_def_axiom", [])


# adj_sym is *primitive*: no defining equation. The term
# ``App_pt adj_sym (cons_l a (cons_l b nil_l))`` IS the adjunction
# operation, just as Empty_pt is the empty set. Adj_pt is a HOL-level
# abbreviation for callers' convenience -- it unfolds to the
# corresponding App_pt expression.
ADJ_PT_DEF = define(
    "Adj_pt",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\a:nat0. \\b:nat0. App_pt adj_sym (cons_l a (cons_l b nil_l))",
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


# proj_sym i n is parametric in i, n at the HOL level: each (i, n) gives
# a distinct closed axiom. ``proj_def_axiom_at i n`` is the axiom
# godelnum for that specific (i, n) pair.
#
#   proj_def_axiom_at i n
#     := Eq_pf (App_pt (proj_sym i n) (Var_t 0 ... Var_t (n-1)))
#              (Var_t i)
#
# where the argument list has length n. Closed; no free Var_t beyond
# those that appear bound by the implicit universal quantifier over
# every Var_t. (Stub body: just zero, since we'd need an n-fold cons_l
# builder.)
PROJ_DEF_AXIOM_AT_DEF = define(
    "proj_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\i:nat0. \\n:nat0. 0",  # stub; real body builds the cons_l list of length n
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
    "                (cons_l (Var_t 0) "
    "                  (cons_l (Var_t (SUC0 0)) "
    "                    (cons_l (Var_t (SUC0 (SUC0 0))) "
    "                      (cons_l (Var_t (SUC0 (SUC0 (SUC0 0)))) nil_l))))) "
    "              (Var_t (SUC0 (SUC0 0))))",
)
if_in_true_def_axiom = mk_const("if_in_true_def_axiom", [])


IF_IN_FALSE_DEF_AXIOM_DEF = define(
    "if_in_false_def_axiom",
    parse_type("nat0"),
    "Imp_pf (Not_pf (In_pa (Var_t 0) (Var_t (SUC0 0)))) "
    "       (Eq_pf (App_pt if_in_sym "
    "                (cons_l (Var_t 0) "
    "                  (cons_l (Var_t (SUC0 0)) "
    "                    (cons_l (Var_t (SUC0 (SUC0 0))) "
    "                      (cons_l (Var_t (SUC0 (SUC0 (SUC0 0)))) nil_l))))) "
    "              (Var_t (SUC0 (SUC0 (SUC0 0)))))",
)
if_in_false_def_axiom = mk_const("if_in_false_def_axiom", [])


# rec_sym g h is parametric in g, h. Each (g, h) pair gives two axioms
# (base and step), each a closed nat0 indexed by (g, h).
REC_BASE_DEF_AXIOM_AT_DEF = define(
    "rec_base_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\g:nat0. \\h:nat0. 0",  # stub; real body encodes rec_sym(g,h) base equation
)
rec_base_def_axiom_at = mk_const("rec_base_def_axiom_at", [])


REC_STEP_DEF_AXIOM_AT_DEF = define(
    "rec_step_def_axiom_at",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\g:nat0. \\h:nat0. 0",  # stub; real body encodes rec_sym(g,h) step equation
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
    # Real body (no adj branch: adj_sym is primitive, no defining
    # equation):
    #   n = zero_def_axiom
    #   \/ (?i n0. n = proj_def_axiom_at i n0 /\ nat0_lt i n0)
    #   \/ n = if_in_true_def_axiom
    #   \/ n = if_in_false_def_axiom
    #   \/ (?g h. n = rec_base_def_axiom_at g h
    #             /\ is_pr_sym g /\ is_pr_sym h)
    #   \/ (?g h. n = rec_step_def_axiom_at g h
    #             /\ is_pr_sym g /\ is_pr_sym h)
    "\\n:nat0. F",  # stub body
)
is_pr_def = mk_const("is_pr_def", [])


@proof
def IS_PR_DEF_HOLDS_ZERO(p):
    """|- is_pr_def zero_def_axiom. STUB."""
    p.goal("is_pr_def zero_def_axiom")
    p.sorry()


@proof
def IS_PR_DEF_HOLDS_PROJ(p):
    """|- !i n. nat0_lt i n ==> is_pr_def (proj_def_axiom_at i n). STUB."""
    p.goal(
        "!i n. nat0_lt i n ==> is_pr_def (proj_def_axiom_at i n)",
        types={"i": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


@proof
def IS_PR_DEF_HOLDS_IF_IN_TRUE(p):
    """|- is_pr_def if_in_true_def_axiom. STUB."""
    p.goal("is_pr_def if_in_true_def_axiom")
    p.sorry()


@proof
def IS_PR_DEF_HOLDS_IF_IN_FALSE(p):
    """|- is_pr_def if_in_false_def_axiom. STUB."""
    p.goal("is_pr_def if_in_false_def_axiom")
    p.sorry()


@proof
def IS_PR_DEF_HOLDS_REC_BASE(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h
            ==> is_pr_def (rec_base_def_axiom_at g h). STUB."""
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h "
        "==> is_pr_def (rec_base_def_axiom_at g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.sorry()


@proof
def IS_PR_DEF_HOLDS_REC_STEP(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h
            ==> is_pr_def (rec_step_def_axiom_at g h). STUB."""
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h "
        "==> is_pr_def (rec_step_def_axiom_at g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.sorry()


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
#                        (App_pt g (cons_l (App_pt h_1 args)
#                                            ...
#                                            (cons_l (App_pt h_k args)
#                                                    nil_l)))).
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
#                   args |-> least q s.t. App_pt f (cons_l q args) = T_pt,
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


# is_partial_pr_sym extends is_pr_sym with the mu-closed symbols. PRST
# itself uses is_partial_pr_sym wherever it would use is_pr_sym (since
# find_proof_pr is in this class). Recogniser stub; the AT-equation
# would say:
#     is_partial_pr_sym f  iff  is_pr_sym f
#                               \/  (?g. f = mu_sym g /\ is_partial_pr_sym g).
IS_PARTIAL_PR_SYM_DEF = define(
    "is_partial_pr_sym", parse_type("nat0 -> bool"), "\\f:nat0. F"
)
is_partial_pr_sym = mk_const("is_partial_pr_sym", [])


@proof
def IS_PARTIAL_PR_SYM_MU(p):
    """|- !f. is_partial_pr_sym f ==> is_partial_pr_sym (mu_sym f). STUB."""
    p.goal(
        "!f. is_partial_pr_sym f ==> is_partial_pr_sym (mu_sym f)",
        types={"f": nat0_ty},
    )
    p.sorry()


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
# definable as a REC over the cons_l list. Total: ~10 base-layer
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


numeral_pr_def = define("numeral_pr", parse_type("nat0"), "0")
numeral_pr = mk_const("numeral_pr", [])

substitute_pr_def = define("substitute_pr", parse_type("nat0"), "0")
substitute_pr = mk_const("substitute_pr", [])

diag_pr_def = define("diag_pr", parse_type("nat0"), "0")
diag_pr = mk_const("diag_pr", [])

Proof_PRST_pr_def = define("Proof_PRST_pr", parse_type("nat0"), "0")
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

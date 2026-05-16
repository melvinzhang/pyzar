# ---------------------------------------------------------------------------
# Stage 1 (PRST) -- syntax of Primitive Recursive Set Theory.
# ---------------------------------------------------------------------------
#
# PRST adjoins a *function symbol* for every primitive recursive (PR)
# set function, along with its defining recursion equations.
#
# A PR function ``f`` is a *term constructor*. The PRST term
# ``App_pt f args`` is the value of ``f`` at the argument tuple
# ``args``. PRST proves
#     App_pt f args  =  <body of f's definition>
# by direct unfolding (its defining equation is an axiom). No traces,
# no functionality side proof. Substitute, numeral, diag, Proof_PRST
# all become closed PRST terms with trivial representability theorems.
#
# Encoding choices:
#
#   Term  ::=  Empty | Var num | Tup Term Term | App f_sym Term
#   Form  ::=  Eq Term Term | In Term Term
#           |  Not Form | Imp Form Form
#
# PRST is quantifier-free: free Var_pt indices in a PRST formula are
# implicitly universally closed by the proof system (PROV_PRST_AXIOM +
# the substitution-into-axiom derived rule). There is no Forall_pf.
#
# Argument tuples are encoded with the ``Tup_pt`` term constructor:
# ``Tup_pt a rest`` extends an argument tuple with one more entry on
# the left, bottoming at ``Empty_pt`` for the empty tuple. So a 3-ary
# call ``App_pt f (a, b, c)`` is ``App_pt f (Tup_pt a (Tup_pt b
# (Tup_pt c Empty_pt)))``. ``Tup_pt`` is a purely syntactic ordered
# pair -- it has no set-theoretic interpretation (unlike ``Adj_pt``,
# which lives at the symbol-application level and IS interpreted as HF
# adjunction in the standard model).
#
# Adjunction is *not* a term constructor in PRST; it is the primitive
# binary PR function symbol ``adj_sym`` (see prst_pr). To build "insert
# a into b" PRST writes ``App_pt adj_sym (Tup_pt a (Tup_pt b
# Empty_pt))`` (or the helper alias ``Adj_pt a b`` from prst_pr). This
# keeps the symbol registry uniform -- every PR function applies via
# the same App_pt(f, args) shape.
#
# Tag layout (sharing the nat0 tag space already used by hf_syntax so
# that PRST formulas parse with the existing constructor encoding):
#
#     Empty_pt          :=  0                           (= Empty_t)
#     Var_pt   v        :=  Pair_ord 2 v                (= Var_t v)
#     Eq_pf    t1 t2    :=  Pair_ord 5 (Pair_ord t1 t2) (= Eq_f)
#     Not_pf   F        :=  Pair_ord 6 F                (= Not_f)
#     Imp_pf   F1 F2    :=  Pair_ord 7 (Pair_ord F1 F2) (= Imp_f)
#     In_pa    t1 t2    :=  Pair_ord 10 (Pair_ord t1 t2)(= In_a)
#     App_pt   f args   :=  Pair_ord 11 (Pair_ord f args)
#     Tup_pt   a b      :=  Pair_ord 12 (Pair_ord a b)
#
# ``App_pt`` and ``Tup_pt`` are the only new constructors; the rest
# are re-exported under PRST names from ``hf_syntax`` so downstream
# PRST formulas can share its syntax lemmas about the nat0 encoding.
#
# Per-function-symbol intro (in ``prst_pr``): each PR function symbol
# ``f`` is a closed nat0 (an id), and ``App_pt f (Tup_pt t1 ... Empty_pt)``
# is its application term. The recursion shape of ``f`` is pinned by
# a *defining equation* axiom; ``prst_pr`` introduces a uniform
# recogniser ``is_pr_def`` for those axioms.
#
# The structural recognisers (``is_pterm``, ``is_pform``, ``free_in_p``,
# ``substitute_p``) extend ``hf_syntax``'s analogues with App_pt /
# Tup_pt clauses and *drop* the Forall_f clause entirely (PRST is
# quantifier-free, so there is no binder to subtract and no
# capture-avoidance to handle). Because Tup_pt is binary structural,
# the App_pt branch's "walk the args list" recursion collapses to one
# recursive call on the args sub-term -- no cons_l walker helpers.
# ---------------------------------------------------------------------------


r"""Syntax of PRST (Primitive Recursive Set Theory) encoded as nat0.

Adds the ``App_pt`` and ``Tup_pt`` constructors on top of the nat0
term/formula encoding from ``hf_syntax.py``. See the module-level
comment block for the encoding table.

Layer 0 status: the four recogniser/recursion constants
(``is_pterm`` / ``is_pform`` / ``free_in_p`` / ``substitute_p``) are
real ``define_wf_lt`` definitions. Their MONO obligations are sorry'd
(Layer 2 work); the wf-lt machinery accepts them and produces real
(sorry-tainted) recursion equations for the AT-lemmas below to unfold.

The AT-equation @proof bodies remain stubbed -- those are Layer 2.
"""

from fusion import Var
from basics import mk_const, mk_app
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof
from nat0_order import define_wf_lt, NAT0_LT_TRANS
from hf_sets import PAIR_ORD_INJ, NAT0_LT_PAIR_ORD_L, NAT0_LT_PAIR_ORD_R
from data_type import (
    define_constructor,
    prove_pairord_binary_size_left,
    prove_pairord_binary_size_right,
)
from hf_syntax import (  # re-exported; PRST uses the same encoding for these
    Empty_t,  # noqa: F401  -- body of Empty_pt
    Var_t,  # noqa: F401  -- body of Var_pt
    Eq_f,  # noqa: F401  -- body of Eq_pf
    Not_f,  # noqa: F401  -- body of Not_pf
    Imp_f,  # noqa: F401  -- body of Imp_pf
    In_a,  # noqa: F401  -- body of In_pa
    VAR_T_AT,
    EQ_F_AT,  # noqa: F401  -- re-export
    NOT_F_AT,  # noqa: F401  -- re-export
    IMP_F_AT,  # noqa: F401  -- re-export
    IN_A_AT,  # noqa: F401  -- re-export
    EMPTY_T_DEF,
    # DSL friction: these are private helpers in hf_syntax (leading
    # underscore), but they're load-bearing for every constructor-lemma
    # module that mirrors the encoding scheme. Reaching in through the
    # underscore convention is the pragmatic option; longer-term they
    # should be promoted to public names.
    _NEQ_PAIR_ORD_ZERO,
    _prove_tag_neq,
)


# ---------------------------------------------------------------------------
# Stage 1 (a) -- PRST renames for the shared nat0 constructors.
#
# PRST inherits the term/form constructors from ``hf_syntax`` verbatim.
# Each PRST name is defined as an alias of the corresponding constant
# so that downstream parse-strings can refer to ``Var_pt`` etc.
# ---------------------------------------------------------------------------

EMPTY_PT_DEF = define("Empty_pt", parse_type("nat0"), "Empty_t")
Empty_pt = mk_const("Empty_pt", [])

VAR_PT_DEF = define("Var_pt", parse_type("nat0 -> nat0"), "Var_t")
Var_pt = mk_const("Var_pt", [])

EQ_PF_DEF = define("Eq_pf", parse_type("nat0 -> nat0 -> nat0"), "Eq_f")
Eq_pf = mk_const("Eq_pf", [])

NOT_PF_DEF = define("Not_pf", parse_type("nat0 -> nat0"), "Not_f")
Not_pf = mk_const("Not_pf", [])

IMP_PF_DEF = define("Imp_pf", parse_type("nat0 -> nat0 -> nat0"), "Imp_f")
Imp_pf = mk_const("Imp_pf", [])

IN_PA_DEF = define("In_pa", parse_type("nat0 -> nat0 -> nat0"), "In_a")
In_pa = mk_const("In_pa", [])


# ---------------------------------------------------------------------------
# Stage 1 (b) -- App_pt and Tup_pt: the new term constructors.
#
#     App_pt f args  :=  Pair_ord 11 (Pair_ord f args)
#     Tup_pt a b     :=  Pair_ord 12 (Pair_ord a b)
#
# ``f`` is the godelnum of a PR-function symbol (a closed nat0 chosen
# in ``prst_pr``); ``args`` is a Tup_pt-nested tuple of term godelnums
# bottoming at ``Empty_pt``.
# ---------------------------------------------------------------------------


# Parser-friendly nat0 literal builder. ``"SUC0 " * n + "0"`` parses as
# repeated self-application of SUC0 (type-incorrect); the parser needs
# fully-parenthesised ``SUC0 (SUC0 (... 0))``. ``suc_chain`` synthesises
# that form. Used throughout prst_syntax / prst_pr for tag literals,
# IS_PR_SYM body disjuncts, and AT-equation 'eq:' strings.
def suc_chain(k):
    """Build the parser-friendly nat0 literal ``SUC0 (SUC0 (... 0))`` (k Succs)."""
    s = "0"
    for _ in range(k):
        s = f"SUC0 ({s})"
    return s


# Backwards-compat alias for the original private name.
_suc_chain = suc_chain


_APP_PT_CTOR = define_constructor(
    "App_pt",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\f:nat0. \\args:nat0. "
    f"Pair_ord ({suc_chain(11)}) (Pair_ord f args)",
)
APP_PT_DEF = _APP_PT_CTOR.def_thm
APP_PT_AT = _APP_PT_CTOR.at_thm
App_pt = _APP_PT_CTOR.const


_TUP_PT_CTOR = define_constructor(
    "Tup_pt",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\a:nat0. \\b:nat0. "
    f"Pair_ord ({suc_chain(12)}) (Pair_ord a b)",
)
TUP_PT_DEF = _TUP_PT_CTOR.def_thm
TUP_PT_AT = _TUP_PT_CTOR.at_thm
Tup_pt = _TUP_PT_CTOR.const


# ---------------------------------------------------------------------------
# Stage 1 (c) -- size and injectivity lemmas for App_pt and Tup_pt.
#
# Same shape as the constructor-INJ lemmas in hf_syntax. Proofs: one or
# two applications of NAT0_LT_PAIR_ORD_L / _R chained via NAT0_LT_TRANS
# for size; PAIR_ORD_INJ at slots 0/1 for injectivity.
# ---------------------------------------------------------------------------


# Tag literals (consumed by NAT0_LT_APP_PT_L and NAT0_LT_TUP_PT_L below).
_APP_PT_TAG = suc_chain(11)
_TUP_PT_TAG = suc_chain(12)


NAT0_LT_APP_PT_L = prove_pairord_binary_size_left(
    "NAT0_LT_APP_PT_L",
    "f",
    "args",
    "App_pt",
    APP_PT_AT,
    _APP_PT_TAG,
    NAT0_LT_PAIR_ORD_L,
    NAT0_LT_PAIR_ORD_R,
    NAT0_LT_TRANS,
)
NAT0_LT_APP_PT_R = prove_pairord_binary_size_right(
    "NAT0_LT_APP_PT_R",
    "f",
    "args",
    "App_pt",
    APP_PT_AT,
    _APP_PT_TAG,
    NAT0_LT_PAIR_ORD_R,
    NAT0_LT_TRANS,
)


@proof
def APP_PT_INJ(p):
    """|- !f1 a1 f2 a2. App_pt f1 a1 = App_pt f2 a2 ==> (f1 = f2 /\\ a1 = a2)."""
    from tactics import SPECL, CONJUNCT2

    p.goal(
        "!f1 a1 f2 a2. App_pt f1 a1 = App_pt f2 a2 ==> (f1 = f2 /\\ a1 = a2)",
        types={"f1": nat0_ty, "a1": nat0_ty, "f2": nat0_ty, "a2": nat0_ty},
    )
    p.fix("f1 a1 f2 a2")
    p.assume("h: App_pt f1 a1 = App_pt f2 a2")
    c1 = SPECL([p._parse("f1"), p._parse("a1")], APP_PT_AT)
    c2 = SPECL([p._parse("f2"), p._parse("a2")], APP_PT_AT)
    p.have(
        f"h_po: Pair_ord ({_APP_PT_TAG}) (Pair_ord f1 a1) "
        f"     = Pair_ord ({_APP_PT_TAG}) (Pair_ord f2 a2)"
    ).by_rewrite_of("h", [c1, c2])
    p.have(
        f"h_outer: ({_APP_PT_TAG}) = ({_APP_PT_TAG}) /\\ "
        f"Pair_ord f1 a1 = Pair_ord f2 a2"
    ).by(
        PAIR_ORD_INJ,
        f"({_APP_PT_TAG})",
        "Pair_ord f1 a1",
        f"({_APP_PT_TAG})",
        "Pair_ord f2 a2",
        "h_po",
    )
    p.have("h_inner: Pair_ord f1 a1 = Pair_ord f2 a2").by_thm(
        CONJUNCT2(p.fact("h_outer"))
    )
    p.have("h_split: f1 = f2 /\\ a1 = a2").by(
        PAIR_ORD_INJ, "f1", "a1", "f2", "a2", "h_inner"
    )
    p.thus("f1 = f2 /\\ a1 = a2").by_thm(p.fact("h_split"))


# Tag inequalities for the 3 disjoint-tag pairs we need.
# hf_syntax._TAG_NEQS only ships pairs in {0..10}; the App_pt (11) and
# Tup_pt (12) tags need fresh instances via _prove_tag_neq.
_TAG_NEQ_VAR_APP = _prove_tag_neq("_TAG_NEQ_VAR_APP", 2, 11)
_TAG_NEQ_VAR_TUP = _prove_tag_neq("_TAG_NEQ_VAR_TUP", 2, 12)
_TAG_NEQ_APP_TUP = _prove_tag_neq("_TAG_NEQ_APP_TUP", 11, 12)
_VAR_T_TAG = suc_chain(2)


# ---------------------------------------------------------------------------
# Local mono-step helper: per-disjunct iff for the App_pt-shape disjunct
# in ``_is_pterm_F``.
#
#   (?fn args. n = App_pt fn args /\ P fn /\ f args)
#     = (?fn args. n = App_pt fn args /\ P fn /\ g args)
#
# DSL friction: hf_syntax ships ``mono_iff_binary_right_step`` for the
# ``?a b. n = C a b /\ f b`` shape, but PRST's App_pt disjunct adds the
# non-recursive ``is_pr_sym fn`` predicate between the constructor
# equation and the recursive call. The standard helper doesn't accept an
# extra conjunct, so we adapt its body inline.
# ---------------------------------------------------------------------------


def _mono_iff_app_pt_step(pred_const, size_lemma_r, hyp_th):
    """``(?a b. n = App_pt a b /\\ P a /\\ f b)
        = (?a b. n = App_pt a b /\\ P a /\\ g b)``
    where ``P = pred_const`` is a unary predicate term independent of f/g.
    """
    from tactics import (
        ASSUME, CHOOSE_WITNESS, CONJUNCT1, CONJUNCT2, CONJ, EQ_MP, EXISTS,
        REWRITE_RULE, SPEC, SYM, MP, DEDUCT_ANTISYM_RULE,
    )
    from data_type import _extract_nfg
    from basics import mk_eq, rand, rator
    from axioms import mk_and, mk_exists, dest_exists

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    a_var = Var("a", k_ty)
    b_var = Var("b", k_ty)
    App_pt_t = mk_const("App_pt", [])

    def _bodies(fn):
        ctor_ab = mk_app(App_pt_t, a_var, b_var)
        return mk_and(
            mk_eq(n_t, ctor_ab),
            mk_and(mk_app(pred_const, a_var), mk_app(fn, b_var)),
        )

    body_inner_l = _bodies(f_t)
    body_inner_r = _bodies(g_t)

    LHS = mk_exists(a_var, mk_exists(b_var, body_inner_l))
    RHS = mk_exists(a_var, mk_exists(b_var, body_inner_r))

    from basics import mk_abs

    def _direction(src, target_inner_body, swap_fg):
        h_top = ASSUME(src)
        outer_pred = dest_exists(src)
        chosen_outer = CHOOSE_WITNESS(outer_pred, h_top)
        new_inner_pred = dest_exists(chosen_outer._concl)
        chosen_inner = CHOOSE_WITNESS(new_inner_pred, chosen_outer)
        n_eq_th = CONJUNCT1(chosen_inner)
        rest = CONJUNCT2(chosen_inner)  # P a /\ f b
        pred_th = CONJUNCT1(rest)        # P a
        fb_th = CONJUNCT2(rest)          # f b
        ctor_app = rand(n_eq_th._concl)
        w_b = rand(ctor_app)
        w_a = rand(rator(ctor_app))
        sl_b = SPEC(w_b, SPEC(w_a, size_lemma_r))
        lt_b_n = REWRITE_RULE([SYM(n_eq_th)], sl_b)
        eq_b = MP(SPEC(w_b, hyp_th), lt_b_n)
        if swap_fg:
            gb_out = EQ_MP(SYM(eq_b), fb_th)
        else:
            gb_out = EQ_MP(eq_b, fb_th)
        new_rest = CONJ(pred_th, gb_out)
        new_body = CONJ(n_eq_th, new_rest)
        target_fn = g_t if not swap_fg else f_t
        target_outer_pred_body = mk_abs(a_var, mk_exists(b_var, target_inner_body))
        inner_pred_aw = mk_abs(
            b_var,
            mk_and(
                mk_eq(n_t, mk_app(App_pt_t, w_a, b_var)),
                mk_and(mk_app(pred_const, w_a), mk_app(target_fn, b_var)),
            ),
        )
        inner_th = EXISTS(inner_pred_aw, w_b, new_body)
        outer_th = EXISTS(target_outer_pred_body, w_a, inner_th)
        return outer_th

    R_th = _direction(LHS, body_inner_r, swap_fg=False)
    L_th = _direction(RHS, body_inner_l, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


@proof
def APP_PT_DISJOINT_VAR_T(p):
    """|- !f args v. ~(App_pt f args = Var_t v).

    Tag-disjointness: App_pt has tag 11, Var_t has tag 2.
    """
    from tactics import SPECL, CONJUNCT1, SYM

    p.goal(
        "!f args v. ~(App_pt f args = Var_t v)",
        types={"f": nat0_ty, "args": nat0_ty, "v": nat0_ty},
    )
    p.fix("f args v")
    app_at = SPECL([p._parse("f"), p._parse("args")], APP_PT_AT)
    var_at = SPECL([p._parse("v")], VAR_T_AT)
    with p.suppose("h: App_pt f args = Var_t v"):
        p.have(
            f"h_po: Pair_ord ({_APP_PT_TAG}) (Pair_ord f args) "
            f"     = Pair_ord ({_VAR_T_TAG}) v"
        ).by_rewrite_of("h", [app_at, var_at])
        p.have(
            f"h_inj: ({_APP_PT_TAG}) = ({_VAR_T_TAG}) /\\ Pair_ord f args = v"
        ).by(
            PAIR_ORD_INJ,
            f"({_APP_PT_TAG})",
            "Pair_ord f args",
            f"({_VAR_T_TAG})",
            "v",
            "h_po",
        )
        p.have(f"h_tag: ({_APP_PT_TAG}) = ({_VAR_T_TAG})").by_thm(
            CONJUNCT1(p.fact("h_inj"))
        )
        # _TAG_NEQ_VAR_APP is keyed (lo, hi) = (2, 11), so its conclusion
        # is ~(SUC0^2 0 = SUC0^11 0). Flip h_tag to match.
        p.have(f"h_tag_sym: ({_VAR_T_TAG}) = ({_APP_PT_TAG})").by_thm(
            SYM(p.fact("h_tag"))
        )
        p.have(f"h_neq: ~(({_VAR_T_TAG}) = ({_APP_PT_TAG}))").by_thm(
            _TAG_NEQ_VAR_APP
        )
        p.absurd().by_conj("h_neq", "h_tag_sym")


@proof
def APP_PT_DISJOINT_EMPTY(p):
    """|- !f args. ~(App_pt f args = Empty_t).

    App_pt's code is ``Pair_ord 11 (Pair_ord f args)``; Pair_ord _ _ is
    never 0 by _NEQ_PAIR_ORD_ZERO.
    """
    from tactics import SPECL

    p.goal(
        "!f args. ~(App_pt f args = Empty_t)",
        types={"f": nat0_ty, "args": nat0_ty},
    )
    p.fix("f args")
    app_at = SPECL([p._parse("f"), p._parse("args")], APP_PT_AT)
    with p.suppose("h: App_pt f args = Empty_t"):
        p.have(
            f"h_po: Pair_ord ({_APP_PT_TAG}) (Pair_ord f args) = 0"
        ).by_rewrite_of("h", [app_at, EMPTY_T_DEF])
        p.have(
            f"h_neg: ~(Pair_ord ({_APP_PT_TAG}) (Pair_ord f args) = 0)"
        ).by(_NEQ_PAIR_ORD_ZERO, f"({_APP_PT_TAG})", "Pair_ord f args")
        p.absurd().by_conj("h_neg", "h_po")


NAT0_LT_TUP_PT_L = prove_pairord_binary_size_left(
    "NAT0_LT_TUP_PT_L",
    "a",
    "b",
    "Tup_pt",
    TUP_PT_AT,
    _TUP_PT_TAG,
    NAT0_LT_PAIR_ORD_L,
    NAT0_LT_PAIR_ORD_R,
    NAT0_LT_TRANS,
)
NAT0_LT_TUP_PT_R = prove_pairord_binary_size_right(
    "NAT0_LT_TUP_PT_R",
    "a",
    "b",
    "Tup_pt",
    TUP_PT_AT,
    _TUP_PT_TAG,
    NAT0_LT_PAIR_ORD_R,
    NAT0_LT_TRANS,
)


@proof
def TUP_PT_INJ(p):
    """|- !a1 b1 a2 b2. Tup_pt a1 b1 = Tup_pt a2 b2 ==> (a1 = a2 /\\ b1 = b2)."""
    from tactics import SPECL, CONJUNCT2

    p.goal(
        "!a1 b1 a2 b2. Tup_pt a1 b1 = Tup_pt a2 b2 ==> (a1 = a2 /\\ b1 = b2)",
        types={"a1": nat0_ty, "b1": nat0_ty, "a2": nat0_ty, "b2": nat0_ty},
    )
    p.fix("a1 b1 a2 b2")
    p.assume("h: Tup_pt a1 b1 = Tup_pt a2 b2")
    c1 = SPECL([p._parse("a1"), p._parse("b1")], TUP_PT_AT)
    c2 = SPECL([p._parse("a2"), p._parse("b2")], TUP_PT_AT)
    p.have(
        f"h_po: Pair_ord ({_TUP_PT_TAG}) (Pair_ord a1 b1) "
        f"     = Pair_ord ({_TUP_PT_TAG}) (Pair_ord a2 b2)"
    ).by_rewrite_of("h", [c1, c2])
    p.have(
        f"h_outer: ({_TUP_PT_TAG}) = ({_TUP_PT_TAG}) /\\ "
        f"Pair_ord a1 b1 = Pair_ord a2 b2"
    ).by(
        PAIR_ORD_INJ,
        f"({_TUP_PT_TAG})",
        "Pair_ord a1 b1",
        f"({_TUP_PT_TAG})",
        "Pair_ord a2 b2",
        "h_po",
    )
    p.have("h_inner: Pair_ord a1 b1 = Pair_ord a2 b2").by_thm(
        CONJUNCT2(p.fact("h_outer"))
    )
    p.have("h_split: a1 = a2 /\\ b1 = b2").by(
        PAIR_ORD_INJ, "a1", "b1", "a2", "b2", "h_inner"
    )
    p.thus("a1 = a2 /\\ b1 = b2").by_thm(p.fact("h_split"))


@proof
def TUP_PT_DISJOINT_VAR_T(p):
    """|- !a b v. ~(Tup_pt a b = Var_t v).

    Tag-disjointness: Tup_pt has tag 12, Var_t has tag 2.
    """
    from tactics import SPECL, CONJUNCT1, SYM

    p.goal(
        "!a b v. ~(Tup_pt a b = Var_t v)",
        types={"a": nat0_ty, "b": nat0_ty, "v": nat0_ty},
    )
    p.fix("a b v")
    tup_at = SPECL([p._parse("a"), p._parse("b")], TUP_PT_AT)
    var_at = SPECL([p._parse("v")], VAR_T_AT)
    with p.suppose("h: Tup_pt a b = Var_t v"):
        p.have(
            f"h_po: Pair_ord ({_TUP_PT_TAG}) (Pair_ord a b) "
            f"     = Pair_ord ({_VAR_T_TAG}) v"
        ).by_rewrite_of("h", [tup_at, var_at])
        p.have(
            f"h_inj: ({_TUP_PT_TAG}) = ({_VAR_T_TAG}) /\\ Pair_ord a b = v"
        ).by(
            PAIR_ORD_INJ,
            f"({_TUP_PT_TAG})",
            "Pair_ord a b",
            f"({_VAR_T_TAG})",
            "v",
            "h_po",
        )
        p.have(f"h_tag: ({_TUP_PT_TAG}) = ({_VAR_T_TAG})").by_thm(
            CONJUNCT1(p.fact("h_inj"))
        )
        # _TAG_NEQ_VAR_TUP : ~(SUC0^2 0 = SUC0^12 0). Flip to match.
        p.have(f"h_tag_sym: ({_VAR_T_TAG}) = ({_TUP_PT_TAG})").by_thm(
            SYM(p.fact("h_tag"))
        )
        p.have(f"h_neq: ~(({_VAR_T_TAG}) = ({_TUP_PT_TAG}))").by_thm(
            _TAG_NEQ_VAR_TUP
        )
        p.absurd().by_conj("h_neq", "h_tag_sym")


@proof
def TUP_PT_DISJOINT_EMPTY(p):
    """|- !a b. ~(Tup_pt a b = Empty_t)."""
    from tactics import SPECL

    p.goal("!a b. ~(Tup_pt a b = Empty_t)", types={"a": nat0_ty, "b": nat0_ty})
    p.fix("a b")
    tup_at = SPECL([p._parse("a"), p._parse("b")], TUP_PT_AT)
    with p.suppose("h: Tup_pt a b = Empty_t"):
        p.have(
            f"h_po: Pair_ord ({_TUP_PT_TAG}) (Pair_ord a b) = 0"
        ).by_rewrite_of("h", [tup_at, EMPTY_T_DEF])
        p.have(
            f"h_neg: ~(Pair_ord ({_TUP_PT_TAG}) (Pair_ord a b) = 0)"
        ).by(_NEQ_PAIR_ORD_ZERO, f"({_TUP_PT_TAG})", "Pair_ord a b")
        p.absurd().by_conj("h_neg", "h_po")


@proof
def TUP_PT_DISJOINT_APP_PT(p):
    """|- !a b f args. ~(Tup_pt a b = App_pt f args).

    Tag-disjointness: Tup_pt has tag 12, App_pt has tag 11.
    """
    from tactics import SPECL, CONJUNCT1

    p.goal(
        "!a b f args. ~(Tup_pt a b = App_pt f args)",
        types={"a": nat0_ty, "b": nat0_ty, "f": nat0_ty, "args": nat0_ty},
    )
    p.fix("a b f args")
    tup_at = SPECL([p._parse("a"), p._parse("b")], TUP_PT_AT)
    app_at = SPECL([p._parse("f"), p._parse("args")], APP_PT_AT)
    with p.suppose("h: Tup_pt a b = App_pt f args"):
        p.have(
            f"h_po: Pair_ord ({_TUP_PT_TAG}) (Pair_ord a b) "
            f"     = Pair_ord ({_APP_PT_TAG}) (Pair_ord f args)"
        ).by_rewrite_of("h", [tup_at, app_at])
        p.have(
            f"h_inj: ({_TUP_PT_TAG}) = ({_APP_PT_TAG}) /\\ "
            f"Pair_ord a b = Pair_ord f args"
        ).by(
            PAIR_ORD_INJ,
            f"({_TUP_PT_TAG})",
            "Pair_ord a b",
            f"({_APP_PT_TAG})",
            "Pair_ord f args",
            "h_po",
        )
        p.have(f"h_tag: ({_TUP_PT_TAG}) = ({_APP_PT_TAG})").by_thm(
            CONJUNCT1(p.fact("h_inj"))
        )
        # _TAG_NEQ_APP_TUP is keyed (lo, hi) = (11, 12), so its conclusion
        # is ~(SUC0^11 0 = SUC0^12 0); matches h_tag directly (no SYM).
        p.have(f"h_neq: ~(({_APP_PT_TAG}) = ({_TUP_PT_TAG}))").by_thm(
            _TAG_NEQ_APP_TUP
        )
        # DSL friction: contradiction finder for `=` / `=` against
        # different SUC0-encodings only triggers on operand match; here
        # h_tag : a = b and h_neq : ~(b = a) differ by orientation, so we
        # flip first.
        from tactics import SYM as _SYM

        p.have(f"h_tag_sym: ({_APP_PT_TAG}) = ({_TUP_PT_TAG})").by_thm(
            _SYM(p.fact("h_tag"))
        )
        p.absurd().by_conj("h_neq", "h_tag_sym")


# ---------------------------------------------------------------------------
# Stage 1 (d) -- PR-symbol registry forward declarations.
#
# ``is_pr_sym`` semantically belongs in ``prst_pr.py``, but
# ``_IS_PTERM_F`` below names it in the App_pt branch, so the parser
# needs it to exist at this point. The body is inlined here because
# ``prst_pr.py`` defines the symbolic constants later.
# ---------------------------------------------------------------------------


# Real bodies inlined verbatim (no recursion). The nine base PR symbols
# encode as:
#   zero_sym         = 0
#   adj_sym          = SUC0 0                                          (= 1)
#   proj_sym i n     = Pair_ord (SUC0 (SUC0 0)) (Pair_ord i n)          (tag 2)
#   if_in_sym        = SUC0 (SUC0 (SUC0 0))                             (= 3)
#   rec_sym g h      = Pair_ord (SUC0^4 0) (Pair_ord g h)               (tag 4)
#   const_sym c      = Pair_ord (SUC0^5 0) c                             (tag 5)
#   course_rec_sym g h
#                    = Pair_ord (SUC0^7 0) (Pair_ord g h)               (tag 7)
#   pair_left_sym    = SUC0^8 0                                          (= 8)
#   pair_right_sym   = SUC0^9 0                                          (= 9)
#   pair_ord_sym     = SUC0^10 0                                         (= 10)
# (`mu_sym f = Pair_ord 6 f` is the partial-PR extension, not is_pr_sym.)
# Symbolic names (zero_sym, adj_sym, ...) live in prst_pr.py, so the
# body below uses the underlying nat0 literals / Pair_ord shapes
# directly. `is_pr_sym` is non-recursive: the proj guard `nat0_lt i n`
# and the rec hypotheses on g, h are encoded in the IS_PR_SYM_PROJ /
# IS_PR_SYM_REC lemma statements, not in this body. (`is_partial_pr_sym`
# below is the wf-recursive closure that adds the mu-symbol case.)
#
# course_rec_sym is the Pair_ord-structural-recursion combinator (the
# analogue of rec_sym but recursing on Pair_ord-decomposition rather
# than Adj-decomposition). pair_left_sym / pair_right_sym extract the
# Pair_ord components; together with course_rec they let substitute_pr
# / Proof_PRST_pr handle non-uniform formula constructors (App_pt's
# fn slot in particular) without re-encoding.
IS_PR_SYM_DEF = define(
    "is_pr_sym",
    parse_type("nat0 -> bool"),
    "\\f:nat0. "
    "f = 0 \\/ "
    f"f = {suc_chain(1)} \\/ "
    f"(?i n. f = Pair_ord ({suc_chain(2)}) (Pair_ord i n)) \\/ "
    f"f = {suc_chain(3)} \\/ "
    f"(?g h. f = Pair_ord ({suc_chain(4)}) (Pair_ord g h)) \\/ "
    f"(?c. f = Pair_ord ({suc_chain(5)}) c) \\/ "
    f"(?g h. f = Pair_ord ({suc_chain(7)}) (Pair_ord g h)) \\/ "
    f"f = {suc_chain(8)} \\/ "
    f"f = {suc_chain(9)} \\/ "
    f"f = {suc_chain(10)}",
)
is_pr_sym = mk_const("is_pr_sym", [])


# ---------------------------------------------------------------------------
# Stage 1 (d.5) -- is_partial_pr_sym (the mu-closure of is_pr_sym).
#
#   is_partial_pr_sym f  iff  is_pr_sym f
#                             \/ (?g. f = Pair_ord 6 g /\ is_partial_pr_sym g)
#
# `Pair_ord 6 g` is the bare encoding of `mu_sym g` (the `mu_sym`
# constant itself lives in prst_pr.py alongside the other PR-symbol-id
# constants; this layer stays self-contained by encoding the
# mu-disjunct as the raw Pair_ord shape). The bridge lemma
# IS_PARTIAL_PR_SYM_MU in prst_pr.py packages
# `is_partial_pr_sym (mu_sym f)` from this body.
#
# Well-foundedness: `g < Pair_ord 6 g` by NAT0_LT_PAIR_ORD_R; the wf-lt
# scaffolding folds this into IS_PARTIAL_PR_SYM_DEF.
#
# Lives here (not prst_pr) because IS_PTERM's App-branch guard mentions
# is_partial_pr_sym: PRST formulas may contain `App_pt (mu_sym _) _`
# subterms (e.g. `Prov_PRST_internal` mentions `App_pt find_proof_pr`
# where `find_proof_pr = mu_sym Proof_PRST_pr`), so well-formedness has
# to admit mu-headed apps at the syntactic level.
# ---------------------------------------------------------------------------


_IS_PARTIAL_PR_SYM_F_DEF = define(
    "_is_partial_pr_sym_F",
    parse_type("(nat0 -> bool) -> nat0 -> bool"),
    "\\rec:nat0->bool. \\f:nat0. "
    "is_pr_sym f \\/ "
    f"(?g. f = Pair_ord ({suc_chain(6)}) g /\\ rec g)",
)
_IS_PARTIAL_PR_SYM_F = mk_const("_is_partial_pr_sym_F", [])


@proof
def IS_PARTIAL_PR_SYM_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
              ==> _is_partial_pr_sym_F f n = _is_partial_pr_sym_F g n.

    Body has 2 disjuncts: ``is_pr_sym n`` (non-recursive; REFL) and
    ``?g'. n = Pair_ord 6 g' /\\ rec g'`` (unary recursive with ctor =
    ``Pair_ord 6`` partial app, size lemma = NAT0_LT_PAIR_ORD_R at
    a := 6).
    """
    from tactics import REFL, or_chain_collapse, SPEC
    from data_type import mono_iff_unary_step

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> "
        "_is_partial_pr_sym_F f n = _is_partial_pr_sym_F g n",
        types={
            "f": parse_type("nat0 -> bool"),
            "g": parse_type("nat0 -> bool"),
            "n": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    h_th = p.fact("h")
    eq_pr = REFL(p._parse("is_pr_sym n"))
    # DSL friction: mono_iff_unary_step takes ctor as a term, not a
    # constant. Pair_ord-applied-at-6 is a Comb, not a Const, but the
    # factory handles it uniformly (rand stripping unwinds the
    # application chain).
    six = p._parse(suc_chain(6))
    pair6 = mk_app(mk_const("Pair_ord", []), six)
    sz_pair6 = SPEC(six, NAT0_LT_PAIR_ORD_R)  # |- !b. nat0_lt b (Pair_ord 6 b)
    eq_mu = mono_iff_unary_step(pair6, sz_pair6, h_th)
    body_eq = or_chain_collapse([eq_pr, eq_mu])
    p.thus("_is_partial_pr_sym_F f n = _is_partial_pr_sym_F g n").by_unfold(
        body_eq, _IS_PARTIAL_PR_SYM_F_DEF
    )


IS_PARTIAL_PR_SYM_DEF, _IS_PARTIAL_PR_SYM_REC = define_wf_lt(
    "is_partial_pr_sym",
    parse_type("nat0 -> bool"),
    _IS_PARTIAL_PR_SYM_F,
    IS_PARTIAL_PR_SYM_MONO,
)
is_partial_pr_sym = mk_const("is_partial_pr_sym", [])


@proof
def IS_PR_SYM_IMP_PARTIAL(p):
    """|- !f. is_pr_sym f ==> is_partial_pr_sym f.

    DISJ1 lift through the wf-recursion equation -- pure-PR symbols sit
    in the first disjunct of `is_partial_pr_sym`'s body. Used to lift
    every concrete `IS_PR_SYM_*` lemma (ZERO/ADJ/PROJ/IF_IN/REC) to its
    partial-PR counterpart for downstream `is_pterm` checks.
    """
    from tactics import SPEC, SYM

    p.goal("!f. is_pr_sym f ==> is_partial_pr_sym f", types={"f": nat0_ty})
    p.fix("f")
    p.assume("h: is_pr_sym f")
    p.have(
        "h_body: is_pr_sym f \\/ "
        f"(?g. f = Pair_ord ({suc_chain(6)}) g /\\ is_partial_pr_sym g)"
    ).by_disj("h")
    p.have(
        "h_F: _is_partial_pr_sym_F is_partial_pr_sym f"
    ).by_unfold("h_body", _IS_PARTIAL_PR_SYM_F_DEF)
    p.thus("is_partial_pr_sym f").by_eq_mp(
        SYM(SPEC(p._parse("f"), _IS_PARTIAL_PR_SYM_REC)),
        "h_F",
    )


# ---------------------------------------------------------------------------
# Stage 1 (e) -- is_pterm.
#
# Four disjuncts (no Forall_pt -- PRST is quantifier-free; no walker
# helpers -- Tup_pt is binary structural):
#
#   t = Empty_pt
#   \/ ?v.       t = Var_pt v
#   \/ ?a b.     t = Tup_pt a b     /\ f a /\ f b
#   \/ ?fn args. t = App_pt fn args /\ is_partial_pr_sym fn /\ f args
#
# App-branch guard is `is_partial_pr_sym` (not `is_pr_sym`) so PRST
# formulas may contain `App_pt (mu_sym _) _` subterms. The
# total/partial distinction stays visible at the symbol level
# (is_pr_sym still means strict PR); is_pterm just admits the wider
# class. PR-defining-axiom-shape terms still satisfy is_pterm via the
# DISJ1 lift `is_pr_sym fn ==> is_partial_pr_sym fn`.
#
# An arity check is intentionally NOT part of is_pterm: PRST syntax
# only checks that the head is a registered PR/partial-PR symbol and
# that the argument payload is a PRST term. Defining-equation
# recognisers enforce the concrete tuple shapes where they matter.
# ---------------------------------------------------------------------------


_IS_PTERM_F_DEF = define(
    "_is_pterm_F",
    parse_type("(nat0 -> bool) -> nat0 -> bool"),
    "\\f:nat0->bool. \\t:nat0. "
    "t = Empty_pt \\/ "
    "(?v. t = Var_pt v) \\/ "
    "(?a b. t = Tup_pt a b /\\ f a /\\ f b) \\/ "
    "(?fn args. t = App_pt fn args /\\ is_partial_pr_sym fn /\\ f args)",
)
_IS_PTERM_F = mk_const("_is_pterm_F", [])


@proof
def IS_PTERM_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
              ==> _is_pterm_F f n = _is_pterm_F g n.
    """
    from tactics import REFL, or_chain_collapse
    from data_type import mono_iff_binary_step

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> "
        "_is_pterm_F f n = _is_pterm_F g n",
        types={
            "f": parse_type("nat0 -> bool"),
            "g": parse_type("nat0 -> bool"),
            "n": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    h_th = p.fact("h")

    # Disjuncts: Empty_pt, Var_pt (both non-recursive), Tup_pt (binary
    # recursion), App_pt (right recursion with is_partial_pr_sym left
    # guard -- relaxed from is_pr_sym so PRST formulas can mention
    # mu-headed apps like `App_pt find_proof_pr _`).
    eq_empty = REFL(p._parse("n = Empty_pt"))
    eq_var = REFL(p._parse("?v. n = Var_pt v"))
    eq_tup = mono_iff_binary_step(
        Tup_pt, NAT0_LT_TUP_PT_L, NAT0_LT_TUP_PT_R, h_th
    )
    eq_app = _mono_iff_app_pt_step(is_partial_pr_sym, NAT0_LT_APP_PT_R, h_th)
    body_eq = or_chain_collapse([eq_empty, eq_var, eq_tup, eq_app])
    p.thus("_is_pterm_F f n = _is_pterm_F g n").by_unfold(
        body_eq, _IS_PTERM_F_DEF
    )


IS_PTERM_DEF, _IS_PTERM_REC_RAW = define_wf_lt(
    "is_pterm",
    parse_type("nat0 -> bool"),
    _IS_PTERM_F,
    IS_PTERM_MONO,
)
is_pterm = mk_const("is_pterm", [])


# Unfold _is_pterm_F at the recursion equation to get a directly-usable
# body recursion. Mirrors _unfold_rec_via_F_def in hf_syntax, inlined to
# avoid the dependency on a hf-specific helper.
def _unfold_prst_rec(rec_raw, F_def):
    from axioms import dest_forall
    from basics import rand
    from tactics import SPEC, GEN, TRANS, REWRITE_CONV, BETA_NORM

    forall_pred = dest_forall(rec_raw._concl)
    n_local = forall_pred.bvar
    spec = SPEC(n_local, rec_raw)
    rhs = rand(spec._concl)
    eq_unfold = REWRITE_CONV([F_def], rhs)
    eq_beta = BETA_NORM(rand(eq_unfold._concl))
    rhs_eq = TRANS(eq_unfold, eq_beta)
    return GEN(n_local, TRANS(spec, rhs_eq))


IS_PTERM_REC = _unfold_prst_rec(_IS_PTERM_REC_RAW, _IS_PTERM_F_DEF)


# ---------------------------------------------------------------------------
# PRST-side CtorRegistry, consumed by ``derive_rec_eq`` and friends.
#
# Two pieces of derived bookkeeping needed:
#   1. Injectivity for the Var_pt alias (derived from VAR_T_INJ via the
#      VAR_PT_DEF alias equation).
#   2. PRST-renamed disjointness lemmas:
#      - Var_pt / Tup_pt / App_pt vs Empty_pt (vs the PRST nil, not Empty_t)
#      - (Var_pt, Tup_pt), (Var_pt, App_pt), (Tup_pt, App_pt)
#
# These derivations are one rewrite each through VAR_PT_DEF / EMPTY_PT_DEF.
# ---------------------------------------------------------------------------


@proof
def VAR_PT_INJ(p):
    """|- !a b. Var_pt a = Var_pt b ==> a = b."""
    from hf_syntax import VAR_T_INJ
    from tactics import SPECL, MP

    p.goal("!a b. Var_pt a = Var_pt b ==> a = b")
    p.fix("a b")
    p.assume("h: Var_pt a = Var_pt b")
    # VAR_PT_DEF : Var_pt = Var_t, so rewriting yields Var_t a = Var_t b.
    p.have("h2: Var_t a = Var_t b").by_rewrite_of("h", [VAR_PT_DEF])
    p.thus("a = b").by_thm(
        MP(SPECL([p._parse("a"), p._parse("b")], VAR_T_INJ), p.fact("h2"))
    )


@proof
def VAR_PT_NEQ_EMPTY_PT(p):
    """|- !v. ~(Var_pt v = Empty_pt)."""
    from hf_syntax import VAR_T_NEQ_EMPTY

    p.goal("!v. ~(Var_pt v = Empty_pt)", types={"v": nat0_ty})
    p.fix("v")
    with p.suppose("h: Var_pt v = Empty_pt"):
        # Rewrite through aliases to obtain Var_t v = Empty_t, contradicting
        # VAR_T_NEQ_EMPTY.
        p.have("h2: Var_t v = Empty_t").by_rewrite_of(
            "h", [VAR_PT_DEF, EMPTY_PT_DEF]
        )
        p.have("neg: ~(Var_t v = Empty_t)").by(VAR_T_NEQ_EMPTY, "v")
        p.absurd().by_conj("neg", "h2")


@proof
def TUP_PT_NEQ_EMPTY_PT(p):
    """|- !a b. ~(Tup_pt a b = Empty_pt)."""
    p.goal(
        "!a b. ~(Tup_pt a b = Empty_pt)", types={"a": nat0_ty, "b": nat0_ty}
    )
    p.fix("a b")
    with p.suppose("h: Tup_pt a b = Empty_pt"):
        p.have("h2: Tup_pt a b = Empty_t").by_rewrite_of("h", [EMPTY_PT_DEF])
        p.have("neg: ~(Tup_pt a b = Empty_t)").by(TUP_PT_DISJOINT_EMPTY, "a", "b")
        p.absurd().by_conj("neg", "h2")


@proof
def APP_PT_NEQ_EMPTY_PT(p):
    """|- !f args. ~(App_pt f args = Empty_pt)."""
    p.goal(
        "!f args. ~(App_pt f args = Empty_pt)",
        types={"f": nat0_ty, "args": nat0_ty},
    )
    p.fix("f args")
    with p.suppose("h: App_pt f args = Empty_pt"):
        p.have("h2: App_pt f args = Empty_t").by_rewrite_of("h", [EMPTY_PT_DEF])
        p.have("neg: ~(App_pt f args = Empty_t)").by(
            APP_PT_DISJOINT_EMPTY, "f", "args"
        )
        p.absurd().by_conj("neg", "h2")


@proof
def VAR_PT_NEQ_TUP_PT(p):
    """|- !v a b. ~(Var_pt v = Tup_pt a b).

    Symmetric flip of TUP_PT_DISJOINT_VAR_T (which uses Var_t naming),
    plus alias rewrite. The disjointness-key in the registry follows the
    natural alphabetical order seen in IS_PTERM_F's body (Var_pt comes
    before Tup_pt in the disjunction ordering).
    """
    p.goal(
        "!v a b. ~(Var_pt v = Tup_pt a b)",
        types={"v": nat0_ty, "a": nat0_ty, "b": nat0_ty},
    )
    p.fix("v a b")
    with p.suppose("h: Var_pt v = Tup_pt a b"):
        from tactics import SYM as _SYM

        p.have("h_sym: Tup_pt a b = Var_pt v").by_thm(_SYM(p.fact("h")))
        p.have("h2: Tup_pt a b = Var_t v").by_rewrite_of("h_sym", [VAR_PT_DEF])
        p.have("neg: ~(Tup_pt a b = Var_t v)").by(
            TUP_PT_DISJOINT_VAR_T, "a", "b", "v"
        )
        p.absurd().by_conj("neg", "h2")


@proof
def VAR_PT_NEQ_APP_PT(p):
    """|- !v f args. ~(Var_pt v = App_pt f args)."""
    p.goal(
        "!v f args. ~(Var_pt v = App_pt f args)",
        types={"v": nat0_ty, "f": nat0_ty, "args": nat0_ty},
    )
    p.fix("v f args")
    with p.suppose("h: Var_pt v = App_pt f args"):
        from tactics import SYM as _SYM

        p.have("h_sym: App_pt f args = Var_pt v").by_thm(_SYM(p.fact("h")))
        p.have("h2: App_pt f args = Var_t v").by_rewrite_of("h_sym", [VAR_PT_DEF])
        p.have("neg: ~(App_pt f args = Var_t v)").by(
            APP_PT_DISJOINT_VAR_T, "f", "args", "v"
        )
        p.absurd().by_conj("neg", "h2")


# ---------------------------------------------------------------------------
# PRST_REGISTRY: feeds ``derive_rec_eq`` for the IS_PTERM AT-equations.
#
# The registry shape mirrors hf_syntax's HF_REGISTRY. ctor declarations
# carry the name and var_names list (the other tuple slots are unused
# by derive_rec_eq's hot path so we pad with ``None``).
# ---------------------------------------------------------------------------
from data_type import CtorRegistry as _CtorRegistry

_PRST_CTORS = {
    "Var_pt": ("Var_pt", None, None, ["v"], None),
    "Tup_pt": ("Tup_pt", None, None, ["a", "b"], None),
    "App_pt": ("App_pt", None, None, ["f", "args"], None),
}

_PRST_INJ = {
    "Var_pt": VAR_PT_INJ,
    "Tup_pt": TUP_PT_INJ,
    "App_pt": APP_PT_INJ,
}

# Pairwise disjointness, keyed by (a_name, b_name) in the order they
# appear in the IS_PTERM body's disjunction.
_PRST_CTOR_DISJOINTNESS = {
    ("Var_pt", "Tup_pt"): VAR_PT_NEQ_TUP_PT,
    ("Var_pt", "App_pt"): VAR_PT_NEQ_APP_PT,
    ("Tup_pt", "App_pt"): TUP_PT_DISJOINT_APP_PT,
}

_PRST_NEQ_EMPTY = {
    "Var_pt": VAR_PT_NEQ_EMPTY_PT,
    "Tup_pt": TUP_PT_NEQ_EMPTY_PT,
    "App_pt": APP_PT_NEQ_EMPTY_PT,
}

PRST_REGISTRY = _CtorRegistry(
    ctors=_PRST_CTORS,
    inj=_PRST_INJ,
    disjointness=_PRST_CTOR_DISJOINTNESS,
    neq_empty=_PRST_NEQ_EMPTY,
    empty_name="Empty_pt",
)


# AT-equations: now derive_rec_eq with PRST_REGISTRY handles each one.
from data_type import derive_rec_eq as _derive_rec_eq


# Empty_pt's AT is the trivial T-shape; derive_rec_eq doesn't ship a
# nullary path (the hf side likewise skips IS_TERM_AT_EMPTY). Manual
# proof via the REC + left-disjunct REFL.
@proof
def IS_PTERM_AT_EMPTY(p):
    """|- is_pterm Empty_pt."""
    from tactics import SPEC, REFL, SYM

    p.goal("is_pterm Empty_pt")
    rec_at = SPEC(p._parse("Empty_pt"), IS_PTERM_REC)
    body = (
        "Empty_pt = Empty_pt \\/ "
        "(?v. Empty_pt = Var_pt v) \\/ "
        "(?a b. Empty_pt = Tup_pt a b /\\ is_pterm a /\\ is_pterm b) \\/ "
        "(?fn args. Empty_pt = App_pt fn args "
        "/\\ is_partial_pr_sym fn /\\ is_pterm args)"
    )
    p.have(f"rec_at: is_pterm Empty_pt = ({body})").by_thm(rec_at)
    p.have("hr: Empty_pt = Empty_pt").by_thm(REFL(p._parse("Empty_pt")))
    p.have(f"disj: {body}").by_disj("hr")
    p.thus("is_pterm Empty_pt").by_eq_mp(SYM(p.fact("rec_at")), "disj")


# derive_rec_eq dispatches each disjunct: the matching constructor's
# injectivity gives a one-point form; the others collapse to F via the
# PRST_REGISTRY disjointness lemmas.
def _strip_eqT(th):
    """``|- !vs. P = T`` -> ``|- !vs. P``. derive_rec_eq's body-less
    matched disjunct (e.g. ``?w. n = Var_pt w``) reduces to ``T`` after
    the existential is witnessed via REFL; the natural consumer interface
    is the bare assertion, so we EQT_ELIM under the foralls."""
    from tactics import EQT_ELIM
    from axioms import dest_forall

    bvars = []
    cur = th
    while dest_forall(cur._concl) is not None:
        from tactics import SPEC

        bvar = dest_forall(cur._concl).bvar
        bvars.append(bvar)
        cur = SPEC(bvar, cur)
    elim = EQT_ELIM(cur)
    from tactics import GEN

    for bvar in reversed(bvars):
        elim = GEN(bvar, elim)
    return elim


IS_PTERM_AT_VAR = _strip_eqT(
    _derive_rec_eq(IS_PTERM_REC, "Var_pt", ["v"], registry=PRST_REGISTRY)
)
IS_PTERM_AT_TUP = _derive_rec_eq(
    IS_PTERM_REC, "Tup_pt", ["a", "b"], registry=PRST_REGISTRY
)
IS_PTERM_AT_APP = _derive_rec_eq(
    IS_PTERM_REC, "App_pt", ["f", "args"], registry=PRST_REGISTRY
)


# ---------------------------------------------------------------------------
# Stage 1 (e.5) -- PRST formula-constructor registry entries.
#
# is_pform / free_in_p / substitute_p mention Eq_pf / In_pa / Not_pf /
# Imp_pf in their bodies. The MONO helpers (mono_iff_*_step) and the
# derive_rec_eq dispatcher require size, INJ, and disjointness lemmas
# stated against the *same* constants used in the body. PRST aliases
# (Eq_pf = Eq_f, etc) are fresh constants distinct from their hf-side
# originals, so hf-side lemmas don't fire directly.
#
# DSL friction: we transport hf-side lemmas through REWRITE_RULE with
# SYM of the alias DEFs. The constant rewrites cleanly because alias
# DEFs assert ``C_prst = C_hf`` at the constant level. A library helper
# wrapping this transport would deduplicate ~14 calls; for now it lives
# as ``_alias_transport`` below.
# ---------------------------------------------------------------------------


from hf_syntax import (  # noqa: E402  -- depends on PRST alias DEFs above
    NAT0_LT_EQ_F_L, NAT0_LT_EQ_F_R,
    NAT0_LT_NOT_F,
    NAT0_LT_IMP_F_L, NAT0_LT_IMP_F_R,
    NAT0_LT_IN_A_L, NAT0_LT_IN_A_R,
    EQ_F_INJ, NOT_F_INJ, IMP_F_INJ, IN_A_INJ,
    EQ_F_NEQ_EMPTY, NOT_F_NEQ_EMPTY, IMP_F_NEQ_EMPTY, IN_A_NEQ_EMPTY,
    CTOR_DISJOINTNESS as _HF_CTOR_DISJOINTNESS,
)
from tactics import REWRITE_RULE as _REWRITE_RULE, SYM as _SYM_T  # noqa: E402


def _alias_transport(hf_thm, *alias_defs):
    """Rewrite occurrences of hf-side constants in ``hf_thm`` to their
    PRST aliases via ``SYM`` of each ``alias_def`` (which states
    ``C_prst = C_hf``)."""
    return _REWRITE_RULE([_SYM_T(d) for d in alias_defs], hf_thm)


NAT0_LT_EQ_PF_L = _alias_transport(NAT0_LT_EQ_F_L, EQ_PF_DEF)
NAT0_LT_EQ_PF_R = _alias_transport(NAT0_LT_EQ_F_R, EQ_PF_DEF)
NAT0_LT_NOT_PF = _alias_transport(NAT0_LT_NOT_F, NOT_PF_DEF)
NAT0_LT_IMP_PF_L = _alias_transport(NAT0_LT_IMP_F_L, IMP_PF_DEF)
NAT0_LT_IMP_PF_R = _alias_transport(NAT0_LT_IMP_F_R, IMP_PF_DEF)
NAT0_LT_IN_PA_L = _alias_transport(NAT0_LT_IN_A_L, IN_PA_DEF)
NAT0_LT_IN_PA_R = _alias_transport(NAT0_LT_IN_A_R, IN_PA_DEF)

EQ_PF_INJ = _alias_transport(EQ_F_INJ, EQ_PF_DEF)
NOT_PF_INJ = _alias_transport(NOT_F_INJ, NOT_PF_DEF)
IMP_PF_INJ = _alias_transport(IMP_F_INJ, IMP_PF_DEF)
IN_PA_INJ = _alias_transport(IN_A_INJ, IN_PA_DEF)

# Pairwise disjointness for {Eq_pf, In_pa, Not_pf, Imp_pf} -- 6 pairs.
# hf-side keys are ordered (Eq_f < Not_f < Imp_f < In_a) per _CTOR_NAMES.
EQ_PF_NEQ_NOT_PF = _alias_transport(
    _HF_CTOR_DISJOINTNESS[("Eq_f", "Not_f")], EQ_PF_DEF, NOT_PF_DEF
)
EQ_PF_NEQ_IMP_PF = _alias_transport(
    _HF_CTOR_DISJOINTNESS[("Eq_f", "Imp_f")], EQ_PF_DEF, IMP_PF_DEF
)
EQ_PF_NEQ_IN_PA = _alias_transport(
    _HF_CTOR_DISJOINTNESS[("Eq_f", "In_a")], EQ_PF_DEF, IN_PA_DEF
)
NOT_PF_NEQ_IMP_PF = _alias_transport(
    _HF_CTOR_DISJOINTNESS[("Not_f", "Imp_f")], NOT_PF_DEF, IMP_PF_DEF
)
NOT_PF_NEQ_IN_PA = _alias_transport(
    _HF_CTOR_DISJOINTNESS[("Not_f", "In_a")], NOT_PF_DEF, IN_PA_DEF
)
IMP_PF_NEQ_IN_PA = _alias_transport(
    _HF_CTOR_DISJOINTNESS[("Imp_f", "In_a")], IMP_PF_DEF, IN_PA_DEF
)


# Extend PRST_REGISTRY's dicts in place. The namedtuple itself holds
# references to the same dicts, so subsequent registry reads observe
# the new entries; the already-derived IS_PTERM_AT_* are unaffected.
_PRST_CTORS.update({
    "Eq_pf": ("Eq_pf", None, None, ["a", "b"], None),
    "In_pa": ("In_pa", None, None, ["a", "b"], None),
    "Not_pf": ("Not_pf", None, None, ["x"], None),
    "Imp_pf": ("Imp_pf", None, None, ["a", "b"], None),
})
_PRST_INJ.update({
    "Eq_pf": EQ_PF_INJ,
    "In_pa": IN_PA_INJ,
    "Not_pf": NOT_PF_INJ,
    "Imp_pf": IMP_PF_INJ,
})
# Keys must match each lemma's actual ``~(A ? = B ?)`` orientation
# (not the body's disjunct order); ``_spec_neq_at`` reads the first
# name in the key as the LHS-ctor. The alias-transported lemmas
# inherit hf_syntax's _CTOR_NAMES ordering: Eq_f < Not_f < Imp_f < In_a,
# so PRST keys follow Eq_pf < Not_pf < Imp_pf < In_pa.
#
# DSL friction: it's tempting to key by body-disjunct order (the
# convenient mnemonic), but that causes ``_spec_neq_at`` to SPECL
# args in the wrong slots and the resulting ``~(LHS = RHS)`` term has
# its arguments shuffled across the ctors -- the MP against
# ``head_eq_th`` then fails with a confusing ``EQ_MP`` error far
# downstream.
_PRST_CTOR_DISJOINTNESS.update({
    ("Eq_pf", "Not_pf"): EQ_PF_NEQ_NOT_PF,
    ("Eq_pf", "Imp_pf"): EQ_PF_NEQ_IMP_PF,
    ("Eq_pf", "In_pa"): EQ_PF_NEQ_IN_PA,
    ("Not_pf", "Imp_pf"): NOT_PF_NEQ_IMP_PF,
    ("Not_pf", "In_pa"): NOT_PF_NEQ_IN_PA,
    ("Imp_pf", "In_pa"): IMP_PF_NEQ_IN_PA,
})


# Cross-group disjointness for free_in_p / substitute_p, which mention
# both term ctors (Var_pt, Tup_pt, App_pt) and formula ctors (Eq_pf,
# In_pa, Not_pf, Imp_pf) in the same body.
#
# DSL friction: hf_syntax's ``_proof_ctor_disjoint`` reads tag / AT
# data from the module-level ``_CTORS`` and tag inequalities from
# ``_TAG_NEQS``. PRST's Tup_pt/App_pt aren't registered there, and
# tag-neqs for pairs (lo, hi) with hi > 10 aren't built (the loop
# only goes up to (10, 11) exclusive). Monkey-patch both dicts with
# the missing entries, then reuse the factory. The alternative --
# writing 8 fresh @proof blocks following the existing
# TUP_PT_DISJOINT_APP_PT template -- would be ~200 lines.
from hf_syntax import (  # noqa: E402
    _CTORS as _HF_CTORS,
    _TAG_NEQS as _HF_TAG_NEQS,
    _proof_ctor_disjoint as _HF_PROOF_CTOR_DISJOINT,
    _ctor_decl as _HF_CTOR_DECL,
    _prove_tag_neq as _HF_PROVE_TAG_NEQ,
)


for _lo in (5, 6, 7, 10):
    for _hi in (11, 12):
        if (_lo, _hi) not in _HF_TAG_NEQS:
            _HF_TAG_NEQS[(_lo, _hi)] = _HF_PROVE_TAG_NEQ(
                f"_TAG_NEQ_{_lo}_{_hi}", _lo, _hi
            )


_HF_CTORS.setdefault(
    "App_pt", _HF_CTOR_DECL("App_pt", APP_PT_AT, 11, ["f", "args"], _APP_PT_TAG)
)
_HF_CTORS.setdefault(
    "Tup_pt", _HF_CTOR_DECL("Tup_pt", TUP_PT_AT, 12, ["a", "b"], _TUP_PT_TAG)
)


# 8 cross-pair disjointness lemmas. Lemma orientation follows the
# order of arguments to _HF_PROOF_CTOR_DISJOINT: LHS=first ctor,
# RHS=second. We build at the hf-side names first (Eq_f, Not_f,
# Imp_f, In_a are in _CTORS; PRST aliases are not), then
# alias-transport with the corresponding *_PF_DEF / IN_PA_DEF to
# rename LHS to the PRST alias. Tup_pt / App_pt are native, no
# transport on the RHS side.
_PRST_ALIAS = {
    "Eq_pf": ("Eq_f", EQ_PF_DEF),
    "Not_pf": ("Not_f", NOT_PF_DEF),
    "Imp_pf": ("Imp_f", IMP_PF_DEF),
    "In_pa": ("In_a", IN_PA_DEF),
}
for _prst_alias_name, (_hf_base_name, _alias_def) in _PRST_ALIAS.items():
    for _prst_name in ("App_pt", "Tup_pt"):
        _hf_lemma = _HF_PROOF_CTOR_DISJOINT(
            f"{_hf_base_name.upper()}_NEQ_{_prst_name.upper()}",
            _hf_base_name,
            _prst_name,
        )
        _PRST_CTOR_DISJOINTNESS[(_prst_alias_name, _prst_name)] = (
            _alias_transport(_hf_lemma, _alias_def)
        )


# 4 Var_pt × formula-ctor pairs via alias transport (Var_pt = Var_t).
VAR_PT_NEQ_EQ_PF = _alias_transport(
    _HF_CTOR_DISJOINTNESS[("Var_t", "Eq_f")], VAR_PT_DEF, EQ_PF_DEF
)
VAR_PT_NEQ_NOT_PF = _alias_transport(
    _HF_CTOR_DISJOINTNESS[("Var_t", "Not_f")], VAR_PT_DEF, NOT_PF_DEF
)
VAR_PT_NEQ_IMP_PF = _alias_transport(
    _HF_CTOR_DISJOINTNESS[("Var_t", "Imp_f")], VAR_PT_DEF, IMP_PF_DEF
)
VAR_PT_NEQ_IN_PA = _alias_transport(
    _HF_CTOR_DISJOINTNESS[("Var_t", "In_a")], VAR_PT_DEF, IN_PA_DEF
)
_PRST_CTOR_DISJOINTNESS.update({
    ("Var_pt", "Eq_pf"): VAR_PT_NEQ_EQ_PF,
    ("Var_pt", "Not_pf"): VAR_PT_NEQ_NOT_PF,
    ("Var_pt", "Imp_pf"): VAR_PT_NEQ_IMP_PF,
    ("Var_pt", "In_pa"): VAR_PT_NEQ_IN_PA,
})


# Neq-empty for the formula ctors. Empty_pt's substitute_p disjunct is
# the matched case for SUBSTITUTE_P_AT_EMPTY; the other 7 disjuncts
# all need ``~(ctor ... = Empty_pt)`` for the F-collapse, since
# ``_ctor_neq_lemma`` routes Empty_pt-targets through ``neq_empty``.
# Term-ctor neq-empty entries are already in ``_PRST_NEQ_EMPTY`` from
# the Layer 1 constructor lemmas; add the formula-ctor entries via
# alias transport from the hf-side ``*_NEQ_EMPTY`` lemmas (which give
# ``~(C ... = Empty_t)``; both LHS and RHS need transport).
EQ_PF_NEQ_EMPTY_PT = _alias_transport(EQ_F_NEQ_EMPTY, EQ_PF_DEF, EMPTY_PT_DEF)
NOT_PF_NEQ_EMPTY_PT = _alias_transport(NOT_F_NEQ_EMPTY, NOT_PF_DEF, EMPTY_PT_DEF)
IMP_PF_NEQ_EMPTY_PT = _alias_transport(IMP_F_NEQ_EMPTY, IMP_PF_DEF, EMPTY_PT_DEF)
IN_PA_NEQ_EMPTY_PT = _alias_transport(IN_A_NEQ_EMPTY, IN_PA_DEF, EMPTY_PT_DEF)
_PRST_NEQ_EMPTY.update({
    "Eq_pf": EQ_PF_NEQ_EMPTY_PT,
    "Not_pf": NOT_PF_NEQ_EMPTY_PT,
    "Imp_pf": IMP_PF_NEQ_EMPTY_PT,
    "In_pa": IN_PA_NEQ_EMPTY_PT,
})


# Shared variable handles for the recursors' body construction.
_v_n0 = Var("v", nat0_ty)
_t_n0 = Var("t", nat0_ty)
_r_n0 = Var("r", nat0_ty)
_x_n0 = Var("x", nat0_ty)


# ---------------------------------------------------------------------------
# Stage 1 (f) -- is_pform.
#
# Four disjuncts (HF's five minus the Forall_f case). Tup_pt and
# App_pt are term constructors, not formula constructors, so they
# don't appear at this layer -- only as sub-terms of Eq_pf / In_pa.
# ---------------------------------------------------------------------------


_IS_PFORM_F_DEF = define(
    "_is_pform_F",
    parse_type("(nat0 -> bool) -> nat0 -> bool"),
    "\\f:nat0->bool. \\phi:nat0. "
    "(?a b. phi = Eq_pf a b /\\ is_pterm a /\\ is_pterm b) \\/ "
    "(?a b. phi = In_pa a b /\\ is_pterm a /\\ is_pterm b) \\/ "
    "(?x. phi = Not_pf x /\\ f x) \\/ "
    "(?a b. phi = Imp_pf a b /\\ f a /\\ f b)",
)
_IS_PFORM_F = mk_const("_is_pform_F", [])


@proof
def IS_PFORM_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
              ==> _is_pform_F f n = _is_pform_F g n.
    """
    from tactics import REFL, or_chain_collapse
    from data_type import mono_iff_unary_step, mono_iff_binary_step

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> "
        "_is_pform_F f n = _is_pform_F g n",
        types={
            "f": parse_type("nat0 -> bool"),
            "g": parse_type("nat0 -> bool"),
            "n": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    h_th = p.fact("h")

    # Eq_pf and In_pa disjuncts mention is_pterm but not f/g; REFL.
    eq_eq = REFL(p._parse("?a b. n = Eq_pf a b /\\ is_pterm a /\\ is_pterm b"))
    eq_in = REFL(p._parse("?a b. n = In_pa a b /\\ is_pterm a /\\ is_pterm b"))
    eq_not = mono_iff_unary_step(Not_pf, NAT0_LT_NOT_PF, h_th)
    eq_imp = mono_iff_binary_step(
        Imp_pf, NAT0_LT_IMP_PF_L, NAT0_LT_IMP_PF_R, h_th
    )
    body_eq = or_chain_collapse([eq_eq, eq_in, eq_not, eq_imp])
    p.thus("_is_pform_F f n = _is_pform_F g n").by_unfold(
        body_eq, _IS_PFORM_F_DEF
    )


IS_PFORM_DEF, _IS_PFORM_REC_RAW = define_wf_lt(
    "is_pform",
    parse_type("nat0 -> bool"),
    _IS_PFORM_F,
    IS_PFORM_MONO,
)
is_pform = mk_const("is_pform", [])


IS_PFORM_REC = _unfold_prst_rec(_IS_PFORM_REC_RAW, _IS_PFORM_F_DEF)


IS_PFORM_AT_EQ = _derive_rec_eq(
    IS_PFORM_REC, "Eq_pf", ["t1", "t2"], registry=PRST_REGISTRY
)
IS_PFORM_AT_IN = _derive_rec_eq(
    IS_PFORM_REC, "In_pa", ["t1", "t2"], registry=PRST_REGISTRY
)
IS_PFORM_AT_NOT = _derive_rec_eq(
    IS_PFORM_REC, "Not_pf", ["F"], registry=PRST_REGISTRY
)
IS_PFORM_AT_IMP = _derive_rec_eq(
    IS_PFORM_REC, "Imp_pf", ["F1", "F2"], registry=PRST_REGISTRY
)


# ---------------------------------------------------------------------------
# Stage 1 (g) -- free_in_p.
#
# Quantifier-free, so "free" collapses to "occurs in". Seven
# disjuncts; every recursive case is binary or unary (no walker):
#
#   ?x.     phi = Var_pt x     /\ v = x
#   \/ ?a b. phi = Tup_pt a b  /\ (f a v \/ f b v)
#   \/ ?a b. phi = Eq_pf a b   /\ (f a v \/ f b v)
#   \/ ?a b. phi = In_pa a b   /\ (f a v \/ f b v)
#   \/ ?x.   phi = Not_pf x    /\ f x v
#   \/ ?a b. phi = Imp_pf a b  /\ (f a v \/ f b v)
#   \/ ?fn args. phi = App_pt fn args /\ f args v
#
# No Forall_pf branch (and no capture-avoidance ``~(v = a)`` guard
# anywhere -- there is no binder to avoid capture against). Empty_pt
# matches no disjunct, so ``free_in_p Empty_pt v`` is false by default.
# ---------------------------------------------------------------------------


_FREE_IN_P_F_DEF = define(
    "_free_in_p_F",
    parse_type("(nat0 -> nat0 -> bool) -> nat0 -> nat0 -> bool"),
    "\\f:nat0->nat0->bool. \\phi:nat0. \\v:nat0. "
    "(?x. phi = Var_pt x /\\ v = x) \\/ "
    "(?a b. phi = Tup_pt a b /\\ (f a v \\/ f b v)) \\/ "
    "(?a b. phi = Eq_pf a b /\\ (f a v \\/ f b v)) \\/ "
    "(?a b. phi = In_pa a b /\\ (f a v \\/ f b v)) \\/ "
    "(?x. phi = Not_pf x /\\ f x v) \\/ "
    "(?a b. phi = Imp_pf a b /\\ (f a v \\/ f b v)) \\/ "
    "(?fn args. phi = App_pt fn args /\\ f args v)",
)
_FREE_IN_P_F = mk_const("_free_in_p_F", [])


@proof
def FREE_IN_P_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
              ==> _free_in_p_F f n = _free_in_p_F g n.
    """
    from tactics import REFL, or_chain_collapse, ABS
    from data_type import (
        mono_iff_unary_pw_step,
        mono_iff_binary_disj_pw_step,
        _mono_iff_binary_pw_step,
    )
    from basics import mk_app as _mk_app

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> "
        "_free_in_p_F f n = _free_in_p_F g n",
        types={
            "f": parse_type("nat0 -> nat0 -> bool"),
            "g": parse_type("nat0 -> nat0 -> bool"),
            "n": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    h_th = p.fact("h")

    eq_var = REFL(p._parse("?x. n = Var_pt x /\\ v = x"))
    eq_tup = mono_iff_binary_disj_pw_step(
        Tup_pt, NAT0_LT_TUP_PT_L, NAT0_LT_TUP_PT_R, h_th, _v_n0
    )
    eq_eq = mono_iff_binary_disj_pw_step(
        Eq_pf, NAT0_LT_EQ_PF_L, NAT0_LT_EQ_PF_R, h_th, _v_n0
    )
    eq_in = mono_iff_binary_disj_pw_step(
        In_pa, NAT0_LT_IN_PA_L, NAT0_LT_IN_PA_R, h_th, _v_n0
    )
    eq_not = mono_iff_unary_pw_step(Not_pf, NAT0_LT_NOT_PF, h_th, _v_n0)
    eq_imp = mono_iff_binary_disj_pw_step(
        Imp_pf, NAT0_LT_IMP_PF_L, NAT0_LT_IMP_PF_R, h_th, _v_n0
    )
    # App_pt: only the args slot recurses (the fn slot is a PR-symbol
    # godelnum, never re-walked). Body shape is ``f args v`` without
    # the ``~(v = a)`` capture-avoidance guard from Forall_f, so the
    # public ``mono_iff_forall_pw_step`` doesn't fit. DSL friction:
    # hf_syntax ships ``mono_iff_binary_right_step`` (non-pw) but not
    # the pw counterpart, so we reach into the private factory.
    eq_app = _mono_iff_binary_pw_step(
        App_pt,
        None,
        NAT0_LT_APP_PT_R,
        h_th,
        _v_n0,
        rest_builder=lambda fn, a, b, v: _mk_app(fn, b, v),
        recurses_l=False,
    )
    body_eq = or_chain_collapse(
        [eq_var, eq_tup, eq_eq, eq_in, eq_not, eq_imp, eq_app]
    )
    abs_eq = ABS(_v_n0, body_eq)
    p.thus("_free_in_p_F f n = _free_in_p_F g n").by_unfold(
        abs_eq, _FREE_IN_P_F_DEF
    )


FREE_IN_P_DEF, _FREE_IN_P_REC_RAW = define_wf_lt(
    "free_in_p",
    parse_type("nat0 -> nat0 -> bool"),
    _FREE_IN_P_F,
    FREE_IN_P_MONO,
)
free_in_p = mk_const("free_in_p", [])


FREE_IN_P_REC = _unfold_prst_rec(_FREE_IN_P_REC_RAW, _FREE_IN_P_F_DEF)


# Constructor recursion equations via derive_rec_eq_pw. The Var_pt
# disjunct's body is ``v = x``; ``_disjunct_eq_match_unary`` rewrites
# ``x`` to the supplied var name, so FREE_IN_P_AT_VAR's RHS is ``v = u``
# (matching the body's orientation). DSL friction: the stub previously
# asserted ``u = v`` but that's just SYM of the natural derivation, so
# the natural form is exposed instead.
from data_type import derive_rec_eq_pw as _derive_rec_eq_pw


FREE_IN_P_AT_VAR = _derive_rec_eq_pw(
    FREE_IN_P_REC, "Var_pt", ["u"], registry=PRST_REGISTRY
)
FREE_IN_P_AT_TUP = _derive_rec_eq_pw(
    FREE_IN_P_REC, "Tup_pt", ["a", "b"], registry=PRST_REGISTRY
)
# The four AT-equations below (Eq_pf / In_pa / Not_pf / Imp_pf) are
# uniform structural-homomorphism corollaries of free_in_p's recursion
# -- the absence of binders means every non-Var case is just a
# disjunction over the children. They're listed individually for
# downstream rewrite convenience.
FREE_IN_P_AT_EQ = _derive_rec_eq_pw(
    FREE_IN_P_REC, "Eq_pf", ["a", "b"], registry=PRST_REGISTRY
)
FREE_IN_P_AT_IN = _derive_rec_eq_pw(
    FREE_IN_P_REC, "In_pa", ["a", "b"], registry=PRST_REGISTRY
)
FREE_IN_P_AT_NOT = _derive_rec_eq_pw(
    FREE_IN_P_REC, "Not_pf", ["phi"], registry=PRST_REGISTRY
)
FREE_IN_P_AT_IMP = _derive_rec_eq_pw(
    FREE_IN_P_REC, "Imp_pf", ["a", "b"], registry=PRST_REGISTRY
)
FREE_IN_P_AT_APP = _derive_rec_eq_pw(
    FREE_IN_P_REC, "App_pt", ["f", "args"], registry=PRST_REGISTRY
)


# ---------------------------------------------------------------------------
# Stage 1 (h) -- substitute_p.
#
# Eight SELECT-disjuncts (no Forall_pf and no capture-avoidance
# HIT/MISS on bound variables; only Var_pt has a HIT/MISS branch).
# Every non-Var case is purely structural pointwise recursion:
#
#   (phi = Empty_pt /\ r = Empty_pt)
#   \/ ?x. phi = Var_pt x /\
#          ((v = x   /\ r = t)
#           \/ (~(v = x) /\ r = Var_pt x))
#   \/ ?a b. phi = Tup_pt a b /\ r = Tup_pt (f a t v) (f b t v)
#   \/ ?a b. phi = Eq_pf a b  /\ r = Eq_pf  (f a t v) (f b t v)
#   \/ ?a b. phi = In_pa a b  /\ r = In_pa  (f a t v) (f b t v)
#   \/ ?x.   phi = Not_pf x   /\ r = Not_pf (f x t v)
#   \/ ?a b. phi = Imp_pf a b /\ r = Imp_pf (f a t v) (f b t v)
#   \/ ?fn args. phi = App_pt fn args
#                /\ r = App_pt fn (f args t v)
#
# No capture machinery, no SUBSTITUTE_AT_FORALL_HIT/MISS, no
# ``free_for_var`` precondition -- substitution is a pure structural
# rewrite.
# ---------------------------------------------------------------------------


_SUBSTITUTE_P_F_DEF = define(
    "_substitute_p_F",
    parse_type(
        "(nat0 -> nat0 -> nat0 -> nat0) -> nat0 -> nat0 -> nat0 -> nat0"
    ),
    "\\f:nat0->nat0->nat0->nat0. \\phi:nat0. \\t:nat0. \\v:nat0. @r:nat0. "
    "(phi = Empty_pt /\\ r = Empty_pt) \\/ "
    "(?x. phi = Var_pt x /\\ "
    "     ((v = x /\\ r = t) \\/ (~(v = x) /\\ r = Var_pt x))) \\/ "
    "(?a b. phi = Tup_pt a b /\\ r = Tup_pt (f a t v) (f b t v)) \\/ "
    "(?a b. phi = Eq_pf a b /\\ r = Eq_pf (f a t v) (f b t v)) \\/ "
    "(?a b. phi = In_pa a b /\\ r = In_pa (f a t v) (f b t v)) \\/ "
    "(?x. phi = Not_pf x /\\ r = Not_pf (f x t v)) \\/ "
    "(?a b. phi = Imp_pf a b /\\ r = Imp_pf (f a t v) (f b t v)) \\/ "
    "(?fn args. phi = App_pt fn args /\\ r = App_pt fn (f args t v))",
)
_SUBSTITUTE_P_F = mk_const("_substitute_p_F", [])


@proof
def SUBSTITUTE_P_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
              ==> _substitute_p_F f n = _substitute_p_F g n.
    """
    from tactics import REFL, or_chain_collapse, ABS, AP_TERM
    from data_type import (
        mono_iff_value_unary_pw_step,
        mono_iff_value_binary_pw_step,
        _mono_iff_value_binary_pw_step,
        _aty_for_select,
    )
    from basics import (
        mk_eq as _mk_eq,
        mk_app as _mk_app,
        mk_const as _mk_const,
    )
    from axioms import mk_and as _mk_and, mk_or as _mk_or, mk_not as _mk_not, mk_exists as _mk_exists

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) ==> "
        "_substitute_p_F f n = _substitute_p_F g n",
        types={
            "f": parse_type("nat0 -> nat0 -> nat0 -> nat0"),
            "g": parse_type("nat0 -> nat0 -> nat0 -> nat0"),
            "n": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    h_th = p.fact("h")

    n_t = p._parse("n")
    args = [_t_n0, _v_n0]

    # Non-recursive disjuncts: Empty_pt and Var_pt branches mention
    # neither f nor g, so REFL of the body suffices.
    eq_empty = REFL(_mk_and(_mk_eq(n_t, Empty_pt), _mk_eq(_r_n0, Empty_pt)))
    eq_var = REFL(
        _mk_exists(
            _x_n0,
            _mk_and(
                _mk_eq(n_t, _mk_app(Var_pt, _x_n0)),
                _mk_or(
                    _mk_and(_mk_eq(_v_n0, _x_n0), _mk_eq(_r_n0, _t_n0)),
                    _mk_and(
                        _mk_not(_mk_eq(_v_n0, _x_n0)),
                        _mk_eq(_r_n0, _mk_app(Var_pt, _x_n0)),
                    ),
                ),
            ),
        )
    )

    eq_tup = mono_iff_value_binary_pw_step(
        Tup_pt, NAT0_LT_TUP_PT_L, NAT0_LT_TUP_PT_R, h_th, args, _r_n0,
        lambda a, b: _mk_app(Tup_pt, a, b),
    )
    eq_eq = mono_iff_value_binary_pw_step(
        Eq_pf, NAT0_LT_EQ_PF_L, NAT0_LT_EQ_PF_R, h_th, args, _r_n0,
        lambda a, b: _mk_app(Eq_pf, a, b),
    )
    eq_in = mono_iff_value_binary_pw_step(
        In_pa, NAT0_LT_IN_PA_L, NAT0_LT_IN_PA_R, h_th, args, _r_n0,
        lambda a, b: _mk_app(In_pa, a, b),
    )
    eq_not = mono_iff_value_unary_pw_step(
        Not_pf, NAT0_LT_NOT_PF, h_th, args, _r_n0,
        lambda x: _mk_app(Not_pf, x),
    )
    eq_imp = mono_iff_value_binary_pw_step(
        Imp_pf, NAT0_LT_IMP_PF_L, NAT0_LT_IMP_PF_R, h_th, args, _r_n0,
        lambda a, b: _mk_app(Imp_pf, a, b),
    )
    # App_pt: rest = ``r = App_pt fn (f args t v)``. The fn slot is
    # non-recursive (it's just a PR-symbol godelnum); only the args
    # slot recurses. DSL friction: like FREE_IN_P's App_pt case, no
    # public ``mono_iff_value_binary_right_pw_step`` exists -- reach
    # into the private factory with ``recurses_l=False``.
    eq_app = _mono_iff_value_binary_pw_step(
        App_pt,
        None,
        NAT0_LT_APP_PT_R,
        h_th,
        args,
        rest_builder=lambda fn, a, b, ags: _mk_eq(
            _r_n0, _mk_app(App_pt, a, _mk_app(fn, b, *ags))
        ),
        recurses_l=False,
    )

    body_eq = or_chain_collapse(
        [eq_empty, eq_var, eq_tup, eq_eq, eq_in, eq_not, eq_imp, eq_app]
    )
    # ABS over r lifts to ``(\r. body[f]) = (\r. body[g])``;
    # AP_TERM through the @-binder lifts to ``(@r. body[f]) = (@r. body[g])``;
    # then ABS over v and over t to reach the function eq.
    abs_r_eq = ABS(_r_n0, body_eq)
    sel_const = _mk_const("@", [(nat0_ty, _aty_for_select())])
    select_eq = AP_TERM(sel_const, abs_r_eq)
    abs_v_eq = ABS(_v_n0, select_eq)
    abs_t_eq = ABS(_t_n0, abs_v_eq)
    p.thus("_substitute_p_F f n = _substitute_p_F g n").by_unfold(
        abs_t_eq, _SUBSTITUTE_P_F_DEF
    )


SUBSTITUTE_P_DEF, _SUBSTITUTE_P_REC_RAW = define_wf_lt(
    "substitute_p",
    parse_type("nat0 -> nat0 -> nat0 -> nat0"),
    _SUBSTITUTE_P_F,
    SUBSTITUTE_P_MONO,
)
substitute_p = mk_const("substitute_p", [])


SUBSTITUTE_P_REC = _unfold_prst_rec(_SUBSTITUTE_P_REC_RAW, _SUBSTITUTE_P_F_DEF)


# Constructor recursion equations. Six cases reduce to ``r = K`` and
# use ``derive_rec_eq_select``. Var_pt has a HIT/MISS conditional shape
# ``(v = x /\ r = t) \/ (~(v = x) /\ r = Var_pt x)`` and uses
# ``derive_rec_eq_select_cond`` to produce a pair of equations:
#   HIT  : !u t v. v = u  ==> substitute_p (Var_pt u) t v = t
#   MISS : !u t v. ~(v=u) ==> substitute_p (Var_pt u) t v = Var_pt u
#
# DSL friction: the original sorry'd stubs asserted ``!v t. ... = t``
# (HIT) and ``!u v t. ~(u = v) ==> ...`` (MISS) -- both equivalent
# under SYM_EQ but not syntactically the same as the natural
# derivation. We expose the natural form here since no external
# consumer of these names exists yet.
from data_type import (  # noqa: E402
    derive_rec_eq_select as _derive_rec_eq_select,
    derive_rec_eq_select_cond as _derive_rec_eq_select_cond,
)


SUBSTITUTE_P_AT_EMPTY = _derive_rec_eq_select(
    SUBSTITUTE_P_REC, "Empty_pt", [], [_t_n0, _v_n0], registry=PRST_REGISTRY
)
SUBSTITUTE_P_AT_VAR_HIT, SUBSTITUTE_P_AT_VAR_MISS = _derive_rec_eq_select_cond(
    SUBSTITUTE_P_REC, "Var_pt", ["u"], [_t_n0, _v_n0], registry=PRST_REGISTRY
)
SUBSTITUTE_P_AT_TUP = _derive_rec_eq_select(
    SUBSTITUTE_P_REC, "Tup_pt", ["a", "b"], [_t_n0, _v_n0], registry=PRST_REGISTRY
)
SUBSTITUTE_P_AT_EQ = _derive_rec_eq_select(
    SUBSTITUTE_P_REC, "Eq_pf", ["a", "b"], [_t_n0, _v_n0], registry=PRST_REGISTRY
)
SUBSTITUTE_P_AT_IN = _derive_rec_eq_select(
    SUBSTITUTE_P_REC, "In_pa", ["a", "b"], [_t_n0, _v_n0], registry=PRST_REGISTRY
)
SUBSTITUTE_P_AT_NOT = _derive_rec_eq_select(
    SUBSTITUTE_P_REC, "Not_pf", ["phi"], [_t_n0, _v_n0], registry=PRST_REGISTRY
)
SUBSTITUTE_P_AT_IMP = _derive_rec_eq_select(
    SUBSTITUTE_P_REC, "Imp_pf", ["a", "b"], [_t_n0, _v_n0], registry=PRST_REGISTRY
)
SUBSTITUTE_P_AT_APP = _derive_rec_eq_select(
    SUBSTITUTE_P_REC, "App_pt", ["f", "args"], [_t_n0, _v_n0], registry=PRST_REGISTRY
)


# ---------------------------------------------------------------------------
# Closure under substitute -- preservation of is_pterm / is_pform.
# Same shape as SUBSTITUTE_PRESERVES_IS_FORM in hf_syntax, dropping the
# Forall_f case and its EXCLUDED_MIDDLE on (v = a). Quantifier-free
# substitution is pure structural rewrite, so preservation is uniform
# across constructors.
# ---------------------------------------------------------------------------


@proof
def SUBSTITUTE_P_PRESERVES_IS_PTERM(p):
    """|- !s t w. is_pterm s /\\ is_pterm t ==> is_pterm (substitute_p s t w).

    Strong induction on ``s`` using IS_PTERM_REC's disjunctive
    characterisation: Empty_pt / Var_pt v (HIT/MISS on w = v) /
    Tup_pt a b (recurse on both) / App_pt fn args (recurse on args).

    DSL friction: the goal binder is ``w`` instead of ``v`` to avoid
    shadowing with the existential ``?v. s = Var_pt v`` inside
    IS_PTERM_REC. The hf-side analogue avoids the clash because its
    Var case uses ``?x. ...`` -- PRST inherited the ``v`` name from
    its F_DEF.
    """
    from tactics import SPEC, SPECL, SYM, AP_TERM, CONJ
    from classical import EXCLUDED_MIDDLE

    p.goal(
        "!s. !t w. is_pterm s /\\ is_pterm t ==> is_pterm (substitute_p s t w)",
        types={"s": nat0_ty, "t": nat0_ty, "w": nat0_ty},
    )
    is_pterm_const = mk_const("is_pterm", [])

    with p.strong_induction("s", "IH"):
        p.fix("t w")
        p.assume("(h_s, h_t): is_pterm s /\\ is_pterm t")

        rec_at_s = SPEC(p._parse("s"), IS_PTERM_REC)
        p.have(
            "h_disj: s = Empty_pt \\/ (?v. s = Var_pt v) \\/ "
            "(?a b. s = Tup_pt a b /\\ is_pterm a /\\ is_pterm b) \\/ "
            "(?fn args. s = App_pt fn args "
            "          /\\ is_partial_pr_sym fn /\\ is_pterm args)"
        ).by_eq_mp(rec_at_s, "h_s")

        with p.cases_on("h_disj"):
            # --- Empty_pt ---
            with p.case("c_empty: s = Empty_pt"):
                p.have("h_subst: substitute_p s t w = Empty_pt").by_rewrite(
                    ["c_empty", SUBSTITUTE_P_AT_EMPTY]
                )
                ap_eq = AP_TERM(is_pterm_const, p.fact("h_subst"))
                p.thus("is_pterm (substitute_p s t w)").by_eq_mp(
                    ap_eq, IS_PTERM_AT_EMPTY
                )

            # --- Var_pt v (HIT / MISS via EXCLUDED_MIDDLE on w = v) ---
            with p.case("c_var: ?v. s = Var_pt v"):
                with p.cases_on(EXCLUDED_MIDDLE, "w = v"):
                    with p.case("hit: w = v"):
                        p.have(
                            "h_subst_inner: substitute_p (Var_pt v) t w = t"
                        ).by(SUBSTITUTE_P_AT_VAR_HIT, "v", "t", "w", "hit")
                        p.have("h_subst: substitute_p s t w = t").by_rewrite_of(
                            "h_subst_inner", [SYM(p.fact("v_eq"))]
                        )
                        ap_eq = AP_TERM(is_pterm_const, p.fact("h_subst"))
                        p.thus("is_pterm (substitute_p s t w)").by_eq_mp(
                            ap_eq, "h_t"
                        )
                    with p.case("miss: ~(w = v)"):
                        p.have(
                            "h_subst_inner: substitute_p (Var_pt v) t w "
                            "= Var_pt v"
                        ).by(SUBSTITUTE_P_AT_VAR_MISS, "v", "t", "w", "miss")
                        p.have("h_subst: substitute_p s t w = s").by_rewrite_of(
                            "h_subst_inner", [SYM(p.fact("v_eq"))]
                        )
                        ap_eq = AP_TERM(is_pterm_const, p.fact("h_subst"))
                        p.thus("is_pterm (substitute_p s t w)").by_eq_mp(
                            ap_eq, "h_s"
                        )

            # --- Tup_pt a b (recursive on both children) ---
            with p.case(
                "c_tup: ?a b. s = Tup_pt a b /\\ is_pterm a /\\ is_pterm b"
            ):
                p.split("b_eq", "(s_eq, h_a, h_b)")
                p.have("lt_a: nat0_lt a s").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_TUP_PT_L),
                    ["s_eq"],
                )
                p.have("lt_b: nat0_lt b s").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_TUP_PT_R),
                    ["s_eq"],
                )
                p.have("hsub_a: is_pterm (substitute_p a t w)").by(
                    "IH", "a", "lt_a", "t", "w",
                    CONJ(p.fact("h_a"), p.fact("h_t")),
                )
                p.have("hsub_b: is_pterm (substitute_p b t w)").by(
                    "IH", "b", "lt_b", "t", "w",
                    CONJ(p.fact("h_b"), p.fact("h_t")),
                )
                p.have(
                    "h_subst: substitute_p s t w "
                    "= Tup_pt (substitute_p a t w) (substitute_p b t w)"
                ).by_rewrite(["s_eq", SUBSTITUTE_P_AT_TUP])
                at_tup = SPECL(
                    [p._parse("substitute_p a t w"), p._parse("substitute_p b t w")],
                    IS_PTERM_AT_TUP,
                )
                p.have(
                    "h_tup_pterm: is_pterm "
                    "(Tup_pt (substitute_p a t w) (substitute_p b t w))"
                ).by_eq_mp(SYM(at_tup), CONJ(p.fact("hsub_a"), p.fact("hsub_b")))
                p.thus("is_pterm (substitute_p s t w)").by_rewrite_of(
                    "h_tup_pterm", [SYM(p.fact("h_subst"))]
                )

            # --- App_pt fn args (only args recurses; fn is a partial-PR
            # symbol -- relaxed from is_pr_sym, since PRST formulas may
            # contain mu-headed apps).
            with p.case(
                "c_app: ?fn args. s = App_pt fn args "
                "/\\ is_partial_pr_sym fn /\\ is_pterm args"
            ):
                p.split("args_eq", "(s_eq, h_pr, h_args)")
                p.have("lt_args: nat0_lt args s").by_rewrite_of(
                    SPECL(
                        [p._parse("fn"), p._parse("args")], NAT0_LT_APP_PT_R
                    ),
                    ["s_eq"],
                )
                p.have("hsub_args: is_pterm (substitute_p args t w)").by(
                    "IH", "args", "lt_args", "t", "w",
                    CONJ(p.fact("h_args"), p.fact("h_t")),
                )
                p.have(
                    "h_subst: substitute_p s t w "
                    "= App_pt fn (substitute_p args t w)"
                ).by_rewrite(["s_eq", SUBSTITUTE_P_AT_APP])
                at_app = SPECL(
                    [p._parse("fn"), p._parse("substitute_p args t w")],
                    IS_PTERM_AT_APP,
                )
                p.have(
                    "h_app_pterm: is_pterm "
                    "(App_pt fn (substitute_p args t w))"
                ).by_eq_mp(
                    SYM(at_app), CONJ(p.fact("h_pr"), p.fact("hsub_args"))
                )
                p.thus("is_pterm (substitute_p s t w)").by_rewrite_of(
                    "h_app_pterm", [SYM(p.fact("h_subst"))]
                )


@proof
def SUBSTITUTE_P_PRESERVES_IS_PFORM(p):
    """|- !phi t v. is_pform phi /\\ is_term t ==> is_pform (substitute_p phi t v).

    Strong induction on ``phi`` using IS_PFORM_REC's case split
    (Eq_pf / In_pa / Not_pf / Imp_pf). Atomic cases (Eq_pf, In_pa)
    delegate to ``SUBSTITUTE_P_PRESERVES_IS_PTERM`` on each subterm;
    Not_pf / Imp_pf recurse on subforms via the IH.
    """
    from tactics import SPEC, SPECL, SYM, CONJ

    p.goal(
        "!phi. !t v. is_pform phi /\\ is_pterm t "
        "==> is_pform (substitute_p phi t v)",
        types={"phi": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    with p.strong_induction("phi", "IH"):
        p.fix("t v")
        p.assume("(h_phi, h_t): is_pform phi /\\ is_pterm t")

        rec_at_phi = SPEC(p._parse("phi"), IS_PFORM_REC)
        p.have(
            "h_disj: (?a b. phi = Eq_pf a b /\\ is_pterm a /\\ is_pterm b) "
            "\\/ (?a b. phi = In_pa a b /\\ is_pterm a /\\ is_pterm b) "
            "\\/ (?x. phi = Not_pf x /\\ is_pform x) "
            "\\/ (?a b. phi = Imp_pf a b /\\ is_pform a /\\ is_pform b)"
        ).by_eq_mp(rec_at_phi, "h_phi")

        with p.cases_on("h_disj"):
            # --- Eq_pf a b (atomic) ---
            with p.case(
                "c_eq: ?a b. phi = Eq_pf a b /\\ is_pterm a /\\ is_pterm b"
            ):
                p.split("b_eq", "(phi_eq, h_a, h_b)")
                p.have("hsub_a: is_pterm (substitute_p a t v)").by(
                    SUBSTITUTE_P_PRESERVES_IS_PTERM, "a", "t", "v",
                    CONJ(p.fact("h_a"), p.fact("h_t")),
                )
                p.have("hsub_b: is_pterm (substitute_p b t v)").by(
                    SUBSTITUTE_P_PRESERVES_IS_PTERM, "b", "t", "v",
                    CONJ(p.fact("h_b"), p.fact("h_t")),
                )
                p.have(
                    "h_subst: substitute_p phi t v "
                    "= Eq_pf (substitute_p a t v) (substitute_p b t v)"
                ).by_rewrite(["phi_eq", SUBSTITUTE_P_AT_EQ])
                at_eq = SPECL(
                    [p._parse("substitute_p a t v"), p._parse("substitute_p b t v")],
                    IS_PFORM_AT_EQ,
                )
                p.have(
                    "h_eq_form: is_pform "
                    "(Eq_pf (substitute_p a t v) (substitute_p b t v))"
                ).by_eq_mp(SYM(at_eq), CONJ(p.fact("hsub_a"), p.fact("hsub_b")))
                p.thus("is_pform (substitute_p phi t v)").by_rewrite_of(
                    "h_eq_form", [SYM(p.fact("h_subst"))]
                )

            # --- In_pa a b (atomic) ---
            with p.case(
                "c_in: ?a b. phi = In_pa a b /\\ is_pterm a /\\ is_pterm b"
            ):
                p.split("b_eq", "(phi_eq, h_a, h_b)")
                p.have("hsub_a: is_pterm (substitute_p a t v)").by(
                    SUBSTITUTE_P_PRESERVES_IS_PTERM, "a", "t", "v",
                    CONJ(p.fact("h_a"), p.fact("h_t")),
                )
                p.have("hsub_b: is_pterm (substitute_p b t v)").by(
                    SUBSTITUTE_P_PRESERVES_IS_PTERM, "b", "t", "v",
                    CONJ(p.fact("h_b"), p.fact("h_t")),
                )
                p.have(
                    "h_subst: substitute_p phi t v "
                    "= In_pa (substitute_p a t v) (substitute_p b t v)"
                ).by_rewrite(["phi_eq", SUBSTITUTE_P_AT_IN])
                at_in = SPECL(
                    [p._parse("substitute_p a t v"), p._parse("substitute_p b t v")],
                    IS_PFORM_AT_IN,
                )
                p.have(
                    "h_in_form: is_pform "
                    "(In_pa (substitute_p a t v) (substitute_p b t v))"
                ).by_eq_mp(SYM(at_in), CONJ(p.fact("hsub_a"), p.fact("hsub_b")))
                p.thus("is_pform (substitute_p phi t v)").by_rewrite_of(
                    "h_in_form", [SYM(p.fact("h_subst"))]
                )

            # --- Not_pf x (unary; recurse on body) ---
            with p.case("c_not: ?x. phi = Not_pf x /\\ is_pform x"):
                p.split("x_eq", "(phi_eq, h_x)")
                p.have("lt_x: nat0_lt x phi").by_rewrite_of(
                    SPEC(p._parse("x"), NAT0_LT_NOT_PF), ["phi_eq"]
                )
                p.have("hsub_x: is_pform (substitute_p x t v)").by(
                    "IH", "x", "lt_x", "t", "v",
                    CONJ(p.fact("h_x"), p.fact("h_t")),
                )
                p.have(
                    "h_subst: substitute_p phi t v = Not_pf (substitute_p x t v)"
                ).by_rewrite(["phi_eq", SUBSTITUTE_P_AT_NOT])
                at_not = SPEC(p._parse("substitute_p x t v"), IS_PFORM_AT_NOT)
                p.have(
                    "h_not_form: is_pform (Not_pf (substitute_p x t v))"
                ).by_eq_mp(SYM(at_not), "hsub_x")
                p.thus("is_pform (substitute_p phi t v)").by_rewrite_of(
                    "h_not_form", [SYM(p.fact("h_subst"))]
                )

            # --- Imp_pf a b (binary; recurse on both) ---
            with p.case(
                "c_imp: ?a b. phi = Imp_pf a b /\\ is_pform a /\\ is_pform b"
            ):
                p.split("b_eq", "(phi_eq, h_a, h_b)")
                p.have("lt_a: nat0_lt a phi").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_IMP_PF_L),
                    ["phi_eq"],
                )
                p.have("lt_b: nat0_lt b phi").by_rewrite_of(
                    SPECL([p._parse("a"), p._parse("b")], NAT0_LT_IMP_PF_R),
                    ["phi_eq"],
                )
                p.have("hsub_a: is_pform (substitute_p a t v)").by(
                    "IH", "a", "lt_a", "t", "v",
                    CONJ(p.fact("h_a"), p.fact("h_t")),
                )
                p.have("hsub_b: is_pform (substitute_p b t v)").by(
                    "IH", "b", "lt_b", "t", "v",
                    CONJ(p.fact("h_b"), p.fact("h_t")),
                )
                p.have(
                    "h_subst: substitute_p phi t v "
                    "= Imp_pf (substitute_p a t v) (substitute_p b t v)"
                ).by_rewrite(["phi_eq", SUBSTITUTE_P_AT_IMP])
                at_imp = SPECL(
                    [p._parse("substitute_p a t v"), p._parse("substitute_p b t v")],
                    IS_PFORM_AT_IMP,
                )
                p.have(
                    "h_imp_form: is_pform "
                    "(Imp_pf (substitute_p a t v) (substitute_p b t v))"
                ).by_eq_mp(SYM(at_imp), CONJ(p.fact("hsub_a"), p.fact("hsub_b")))
                p.thus("is_pform (substitute_p phi t v)").by_rewrite_of(
                    "h_imp_form", [SYM(p.fact("h_subst"))]
                )


# ---------------------------------------------------------------------------
# Notes on the size of this module.
#
# Compared to the cons_l ArgList variant, this module saves the four
# wf-lt walker definitions (list_length / all_pred / any_pred /
# map_pred) and their MONOs, at the cost of one new term constructor
# (Tup_pt) with the standard 5-lemma boilerplate (size L/R, INJ, two
# disjointness). Net: ~150 lines lighter.
#
# Estimate filled in: ~550 lines.
# ---------------------------------------------------------------------------


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 1 (PRST) -- syntax.")
    print("    APP_PT_DEF             :", pp_thm(APP_PT_DEF))
    print("    TUP_PT_DEF             :", pp_thm(TUP_PT_DEF))
    print("    NAT0_LT_APP_PT_L       :", pp_thm(NAT0_LT_APP_PT_L))
    print("    NAT0_LT_APP_PT_R       :", pp_thm(NAT0_LT_APP_PT_R))
    print("    NAT0_LT_TUP_PT_L       :", pp_thm(NAT0_LT_TUP_PT_L))
    print("    NAT0_LT_TUP_PT_R       :", pp_thm(NAT0_LT_TUP_PT_R))
    print("    APP_PT_INJ             :", pp_thm(APP_PT_INJ))
    print("    TUP_PT_INJ             :", pp_thm(TUP_PT_INJ))
    print("    IS_PTERM_AT_TUP        :", pp_thm(IS_PTERM_AT_TUP))
    print("    IS_PTERM_AT_APP        :", pp_thm(IS_PTERM_AT_APP))
    print("    FREE_IN_P_AT_TUP       :", pp_thm(FREE_IN_P_AT_TUP))
    print("    FREE_IN_P_AT_EQ        :", pp_thm(FREE_IN_P_AT_EQ))
    print("    FREE_IN_P_AT_IN        :", pp_thm(FREE_IN_P_AT_IN))
    print("    FREE_IN_P_AT_NOT       :", pp_thm(FREE_IN_P_AT_NOT))
    print("    FREE_IN_P_AT_IMP       :", pp_thm(FREE_IN_P_AT_IMP))
    print("    FREE_IN_P_AT_APP       :", pp_thm(FREE_IN_P_AT_APP))
    print("    SUBSTITUTE_P_AT_EMPTY  :", pp_thm(SUBSTITUTE_P_AT_EMPTY))
    print("    SUBSTITUTE_P_AT_TUP    :", pp_thm(SUBSTITUTE_P_AT_TUP))
    print("    SUBSTITUTE_P_AT_EQ     :", pp_thm(SUBSTITUTE_P_AT_EQ))
    print("    SUBSTITUTE_P_AT_IN     :", pp_thm(SUBSTITUTE_P_AT_IN))
    print("    SUBSTITUTE_P_AT_NOT    :", pp_thm(SUBSTITUTE_P_AT_NOT))
    print("    SUBSTITUTE_P_AT_IMP    :", pp_thm(SUBSTITUTE_P_AT_IMP))
    print("    SUBSTITUTE_P_AT_APP    :", pp_thm(SUBSTITUTE_P_AT_APP))

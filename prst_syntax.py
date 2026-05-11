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
# is its application term. The arity and recursion shape of ``f`` is
# pinned by a *defining equation* axiom; ``prst_pr`` introduces a
# uniform recogniser ``is_pr_def`` for those axioms.
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
from proof import proof, define_with_at
from nat0_order import define_wf_lt, NAT0_LT_TRANS
from hf_sets import PAIR_ORD_INJ, NAT0_LT_PAIR_ORD_L, NAT0_LT_PAIR_ORD_R
from hf_syntax import (  # re-exported; PRST uses the same encoding for these
    Empty_t,  # noqa: F401  -- body of Empty_pt
    Var_t,
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


_f_n0 = Var("f", nat0_ty)
_args_n0 = Var("args", nat0_ty)


APP_PT_DEF, APP_PT_AT = define_with_at(
    "App_pt",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\f:nat0. \\args:nat0. "
    "Pair_ord "
    "(SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0))))))))))) "
    "(Pair_ord f args)",
)
App_pt = mk_const("App_pt", [])


_a_n0 = Var("a", nat0_ty)
_b_n0 = Var("b", nat0_ty)


TUP_PT_DEF, TUP_PT_AT = define_with_at(
    "Tup_pt",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\a:nat0. \\b:nat0. "
    "Pair_ord "
    "(SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))))))))) "
    "(Pair_ord a b)",
)
Tup_pt = mk_const("Tup_pt", [])


# ---------------------------------------------------------------------------
# Stage 1 (c) -- size and injectivity lemmas for App_pt and Tup_pt.
#
# Same shape as the constructor-INJ lemmas in hf_syntax. Proofs: one or
# two applications of NAT0_LT_PAIR_ORD_L / _R chained via NAT0_LT_TRANS
# for size; PAIR_ORD_INJ at slots 0/1 for injectivity.
# ---------------------------------------------------------------------------


# Tag literals. App_pt has tag SUC0^11 0, Tup_pt has tag SUC0^12 0.
# DSL friction: SUC0-chains must be nested in parens. ``"SUC0 " * n + "0"``
# parses as a chain of applications of SUC0 to itself (type-incorrect);
# need ``SUC0 (SUC0 (... 0))``.
def _suc_chain(k):
    s = "0"
    for _ in range(k):
        s = f"SUC0 ({s})"
    return s


_APP_PT_TAG = _suc_chain(11)
_TUP_PT_TAG = _suc_chain(12)


@proof
def NAT0_LT_APP_PT_L(p):
    """|- !f args. nat0_lt f (App_pt f args)."""
    from tactics import SYM, SPECL

    p.goal(
        "!f args. nat0_lt f (App_pt f args)",
        types={"f": nat0_ty, "args": nat0_ty},
    )
    p.fix("f args")
    app_at = SPECL([p._parse("f"), p._parse("args")], APP_PT_AT)
    p.have("h1: nat0_lt f (Pair_ord f args)").by(NAT0_LT_PAIR_ORD_L, "f", "args")
    p.have(
        f"h2: nat0_lt (Pair_ord f args) "
        f"(Pair_ord ({_APP_PT_TAG}) (Pair_ord f args))"
    ).by(NAT0_LT_PAIR_ORD_R, f"({_APP_PT_TAG})", "Pair_ord f args")
    p.have(
        f"h3: nat0_lt f (Pair_ord ({_APP_PT_TAG}) (Pair_ord f args))"
    ).by(
        NAT0_LT_TRANS,
        "f",
        "Pair_ord f args",
        f"Pair_ord ({_APP_PT_TAG}) (Pair_ord f args)",
        "h1",
        "h2",
    )
    p.thus("nat0_lt f (App_pt f args)").by_rewrite_of("h3", [SYM(app_at)])


@proof
def NAT0_LT_APP_PT_R(p):
    """|- !f args. nat0_lt args (App_pt f args)."""
    from tactics import SYM, SPECL

    p.goal(
        "!f args. nat0_lt args (App_pt f args)",
        types={"f": nat0_ty, "args": nat0_ty},
    )
    p.fix("f args")
    app_at = SPECL([p._parse("f"), p._parse("args")], APP_PT_AT)
    p.have("h1: nat0_lt args (Pair_ord f args)").by(
        NAT0_LT_PAIR_ORD_R, "f", "args"
    )
    p.have(
        f"h2: nat0_lt (Pair_ord f args) "
        f"(Pair_ord ({_APP_PT_TAG}) (Pair_ord f args))"
    ).by(NAT0_LT_PAIR_ORD_R, f"({_APP_PT_TAG})", "Pair_ord f args")
    p.have(
        f"h3: nat0_lt args (Pair_ord ({_APP_PT_TAG}) (Pair_ord f args))"
    ).by(
        NAT0_LT_TRANS,
        "args",
        "Pair_ord f args",
        f"Pair_ord ({_APP_PT_TAG}) (Pair_ord f args)",
        "h1",
        "h2",
    )
    p.thus("nat0_lt args (App_pt f args)").by_rewrite_of("h3", [SYM(app_at)])


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
_VAR_T_TAG = _suc_chain(2)


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
    from hf_syntax import _extract_nfg
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


@proof
def NAT0_LT_TUP_PT_L(p):
    """|- !a b. nat0_lt a (Tup_pt a b)."""
    from tactics import SYM, SPECL

    p.goal("!a b. nat0_lt a (Tup_pt a b)", types={"a": nat0_ty, "b": nat0_ty})
    p.fix("a b")
    tup_at = SPECL([p._parse("a"), p._parse("b")], TUP_PT_AT)
    p.have("h1: nat0_lt a (Pair_ord a b)").by(NAT0_LT_PAIR_ORD_L, "a", "b")
    p.have(
        f"h2: nat0_lt (Pair_ord a b) (Pair_ord ({_TUP_PT_TAG}) (Pair_ord a b))"
    ).by(NAT0_LT_PAIR_ORD_R, f"({_TUP_PT_TAG})", "Pair_ord a b")
    p.have(
        f"h3: nat0_lt a (Pair_ord ({_TUP_PT_TAG}) (Pair_ord a b))"
    ).by(
        NAT0_LT_TRANS,
        "a",
        "Pair_ord a b",
        f"Pair_ord ({_TUP_PT_TAG}) (Pair_ord a b)",
        "h1",
        "h2",
    )
    p.thus("nat0_lt a (Tup_pt a b)").by_rewrite_of("h3", [SYM(tup_at)])


@proof
def NAT0_LT_TUP_PT_R(p):
    """|- !a b. nat0_lt b (Tup_pt a b)."""
    from tactics import SYM, SPECL

    p.goal("!a b. nat0_lt b (Tup_pt a b)", types={"a": nat0_ty, "b": nat0_ty})
    p.fix("a b")
    tup_at = SPECL([p._parse("a"), p._parse("b")], TUP_PT_AT)
    p.have("h1: nat0_lt b (Pair_ord a b)").by(NAT0_LT_PAIR_ORD_R, "a", "b")
    p.have(
        f"h2: nat0_lt (Pair_ord a b) (Pair_ord ({_TUP_PT_TAG}) (Pair_ord a b))"
    ).by(NAT0_LT_PAIR_ORD_R, f"({_TUP_PT_TAG})", "Pair_ord a b")
    p.have(
        f"h3: nat0_lt b (Pair_ord ({_TUP_PT_TAG}) (Pair_ord a b))"
    ).by(
        NAT0_LT_TRANS,
        "b",
        "Pair_ord a b",
        f"Pair_ord ({_TUP_PT_TAG}) (Pair_ord a b)",
        "h1",
        "h2",
    )
    p.thus("nat0_lt b (Tup_pt a b)").by_rewrite_of("h3", [SYM(tup_at)])


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
# needs it to exist at this point. Stubbed; Layer 4 in
# ``prst_sorry.md`` replaces with the real registry body.
#
# (``pr_arity`` is no longer referenced from ``_IS_PTERM_F`` -- the
# arity check moved out of the syntactic recogniser. It is still
# declared here so downstream modules can name it.)
# ---------------------------------------------------------------------------


IS_PR_SYM_DEF = define("is_pr_sym", parse_type("nat0 -> bool"), "\\f:nat0. F")
is_pr_sym = mk_const("is_pr_sym", [])

PR_ARITY_DEF = define("pr_arity", parse_type("nat0 -> nat0"), "\\f:nat0. 0")
pr_arity = mk_const("pr_arity", [])


# ---------------------------------------------------------------------------
# Stage 1 (e) -- is_pterm.
#
# Four disjuncts (no Forall_pt -- PRST is quantifier-free; no walker
# helpers -- Tup_pt is binary structural):
#
#   t = Empty_pt
#   \/ ?v.       t = Var_pt v
#   \/ ?a b.     t = Tup_pt a b     /\ f a /\ f b
#   \/ ?fn args. t = App_pt fn args /\ is_pr_sym fn /\ f args
#
# The arity check (pr_arity fn = length of args) is intentionally NOT
# part of is_pterm -- it would require walking the Tup_pt chain to
# compute a length, which is exactly the walker recursion the Tup_pt
# encoding was chosen to avoid. Arity correctness is enforced at the
# proof-system level (defining-equation axioms only fire for
# correctly-shaped args), not at the syntactic-recogniser level.
# ---------------------------------------------------------------------------


_IS_PTERM_F_DEF = define(
    "_is_pterm_F",
    parse_type("(nat0 -> bool) -> nat0 -> bool"),
    "\\f:nat0->bool. \\t:nat0. "
    "t = Empty_pt \\/ "
    "(?v. t = Var_pt v) \\/ "
    "(?a b. t = Tup_pt a b /\\ f a /\\ f b) \\/ "
    "(?fn args. t = App_pt fn args /\\ is_pr_sym fn /\\ f args)",
)
_IS_PTERM_F = mk_const("_is_pterm_F", [])


@proof
def IS_PTERM_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
              ==> _is_pterm_F f n = _is_pterm_F g n.
    """
    from tactics import REFL, or_chain_collapse
    from hf_syntax import mono_iff_binary_step

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
    # recursion), App_pt (right recursion with is_pr_sym left guard).
    eq_empty = REFL(p._parse("n = Empty_pt"))
    eq_var = REFL(p._parse("?v. n = Var_pt v"))
    eq_tup = mono_iff_binary_step(
        Tup_pt, NAT0_LT_TUP_PT_L, NAT0_LT_TUP_PT_R, h_th
    )
    eq_app = _mono_iff_app_pt_step(is_pr_sym, NAT0_LT_APP_PT_R, h_th)
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
from hf_syntax import CtorRegistry as _CtorRegistry

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
from hf_syntax import derive_rec_eq as _derive_rec_eq


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
        "/\\ is_pr_sym fn /\\ is_pterm args)"
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
              ==> _is_pform_F f n = _is_pform_F g n. STUB (Layer 2).
    """
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
    p.sorry()


IS_PFORM_DEF, _IS_PFORM_REC = define_wf_lt(
    "is_pform",
    parse_type("nat0 -> bool"),
    _IS_PFORM_F,
    IS_PFORM_MONO,
)
is_pform = mk_const("is_pform", [])


@proof
def IS_PFORM_AT_EQ(p):
    """|- !t1 t2. is_pform (Eq_pf t1 t2) = (is_pterm t1 /\\ is_pterm t2). STUB."""
    p.goal(
        "!t1 t2. is_pform (Eq_pf t1 t2) = (is_pterm t1 /\\ is_pterm t2)",
        types={"t1": nat0_ty, "t2": nat0_ty},
    )
    p.sorry()


@proof
def IS_PFORM_AT_IN(p):
    """|- !t1 t2. is_pform (In_pa t1 t2) = (is_pterm t1 /\\ is_pterm t2). STUB."""
    p.goal(
        "!t1 t2. is_pform (In_pa t1 t2) = (is_pterm t1 /\\ is_pterm t2)",
        types={"t1": nat0_ty, "t2": nat0_ty},
    )
    p.sorry()


@proof
def IS_PFORM_AT_NOT(p):
    """|- !F. is_pform (Not_pf F) = is_pform F. STUB."""
    p.goal("!F. is_pform (Not_pf F) = is_pform F", types={"F": nat0_ty})
    p.sorry()


@proof
def IS_PFORM_AT_IMP(p):
    """|- !F1 F2. is_pform (Imp_pf F1 F2) = (is_pform F1 /\\ is_pform F2). STUB."""
    p.goal(
        "!F1 F2. is_pform (Imp_pf F1 F2) = (is_pform F1 /\\ is_pform F2)",
        types={"F1": nat0_ty, "F2": nat0_ty},
    )
    p.sorry()


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
              ==> _free_in_p_F f n = _free_in_p_F g n. STUB (Layer 2).
    """
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
    p.sorry()


FREE_IN_P_DEF, _FREE_IN_P_REC = define_wf_lt(
    "free_in_p",
    parse_type("nat0 -> nat0 -> bool"),
    _FREE_IN_P_F,
    FREE_IN_P_MONO,
)
free_in_p = mk_const("free_in_p", [])


@proof
def FREE_IN_P_AT_VAR(p):
    """|- !u v. free_in_p (Var_pt u) v = (u = v). STUB."""
    p.goal(
        "!u v. free_in_p (Var_pt u) v = (u = v)",
        types={"u": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def FREE_IN_P_AT_TUP(p):
    """|- !a b v. free_in_p (Tup_pt a b) v
                 = (free_in_p a v \\/ free_in_p b v). STUB."""
    p.goal(
        "!a b v. free_in_p (Tup_pt a b) v = (free_in_p a v \\/ free_in_p b v)",
        types={"a": nat0_ty, "b": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


# The four AT-equations below (Eq_pf / In_pa / Not_pf / Imp_pf) are
# uniform structural-homomorphism corollaries of free_in_p's recursion
# -- the absence of binders means every non-Var case is just a
# disjunction over the children. They're listed individually for
# downstream rewrite convenience, not because the cases are substantive
# (in hf_syntax the analogous FREE_IN_AT_FORALL is structurally
# distinct due to capture-avoidance; PRST has no such case).


@proof
def FREE_IN_P_AT_EQ(p):
    """|- !a b v. free_in_p (Eq_pf a b) v
                 = (free_in_p a v \\/ free_in_p b v). STUB."""
    p.goal(
        "!a b v. free_in_p (Eq_pf a b) v = (free_in_p a v \\/ free_in_p b v)",
        types={"a": nat0_ty, "b": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def FREE_IN_P_AT_IN(p):
    """|- !a b v. free_in_p (In_pa a b) v
                 = (free_in_p a v \\/ free_in_p b v). STUB."""
    p.goal(
        "!a b v. free_in_p (In_pa a b) v = (free_in_p a v \\/ free_in_p b v)",
        types={"a": nat0_ty, "b": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def FREE_IN_P_AT_NOT(p):
    """|- !phi v. free_in_p (Not_pf phi) v = free_in_p phi v. STUB."""
    p.goal(
        "!phi v. free_in_p (Not_pf phi) v = free_in_p phi v",
        types={"phi": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def FREE_IN_P_AT_IMP(p):
    """|- !a b v. free_in_p (Imp_pf a b) v
                 = (free_in_p a v \\/ free_in_p b v). STUB."""
    p.goal(
        "!a b v. free_in_p (Imp_pf a b) v = (free_in_p a v \\/ free_in_p b v)",
        types={"a": nat0_ty, "b": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def FREE_IN_P_AT_APP(p):
    """|- !f args v. free_in_p (App_pt f args) v = free_in_p args v. STUB."""
    p.goal(
        "!f args v. free_in_p (App_pt f args) v = free_in_p args v",
        types={"f": nat0_ty, "args": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


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
              ==> _substitute_p_F f n = _substitute_p_F g n. STUB (Layer 2).
    """
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
    p.sorry()


SUBSTITUTE_P_DEF, _SUBSTITUTE_P_REC = define_wf_lt(
    "substitute_p",
    parse_type("nat0 -> nat0 -> nat0 -> nat0"),
    _SUBSTITUTE_P_F,
    SUBSTITUTE_P_MONO,
)
substitute_p = mk_const("substitute_p", [])


@proof
def SUBSTITUTE_P_AT_EMPTY(p):
    """|- !t v. substitute_p Empty_pt t v = Empty_pt. STUB."""
    p.goal(
        "!t v. substitute_p Empty_pt t v = Empty_pt",
        types={"t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def SUBSTITUTE_P_AT_VAR_HIT(p):
    """|- !v t. substitute_p (Var_pt v) t v = t. STUB."""
    p.goal(
        "!v t. substitute_p (Var_pt v) t v = t",
        types={"v": nat0_ty, "t": nat0_ty},
    )
    p.sorry()


@proof
def SUBSTITUTE_P_AT_VAR_MISS(p):
    """|- !u v t. ~(u = v) ==> substitute_p (Var_pt u) t v = Var_pt u. STUB."""
    p.goal(
        "!u v t. ~(u = v) ==> substitute_p (Var_pt u) t v = Var_pt u",
        types={"u": nat0_ty, "v": nat0_ty, "t": nat0_ty},
    )
    p.sorry()


@proof
def SUBSTITUTE_P_AT_TUP(p):
    """|- !a b t v.
            substitute_p (Tup_pt a b) t v
              = Tup_pt (substitute_p a t v) (substitute_p b t v). STUB."""
    p.goal(
        "!a b t v. substitute_p (Tup_pt a b) t v "
        "          = Tup_pt (substitute_p a t v) (substitute_p b t v)",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


# The four AT-equations below (Eq_pf / In_pa / Not_pf / Imp_pf) are
# uniform structural-homomorphism corollaries of substitute_p's
# recursion -- the absence of binders means substitute_p distributes
# through every non-Var constructor without capture-avoidance branching.
# They're listed individually for downstream rewrite convenience, not
# because the cases are substantive (in hf_syntax the analogous
# SUBSTITUTE_AT_FORALL_HIT/MISS are structurally distinct; PRST has
# no such case).


@proof
def SUBSTITUTE_P_AT_EQ(p):
    """|- !a b t v.
            substitute_p (Eq_pf a b) t v
              = Eq_pf (substitute_p a t v) (substitute_p b t v). STUB."""
    p.goal(
        "!a b t v. substitute_p (Eq_pf a b) t v "
        "          = Eq_pf (substitute_p a t v) (substitute_p b t v)",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def SUBSTITUTE_P_AT_IN(p):
    """|- !a b t v.
            substitute_p (In_pa a b) t v
              = In_pa (substitute_p a t v) (substitute_p b t v). STUB."""
    p.goal(
        "!a b t v. substitute_p (In_pa a b) t v "
        "          = In_pa (substitute_p a t v) (substitute_p b t v)",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def SUBSTITUTE_P_AT_NOT(p):
    """|- !phi t v.
            substitute_p (Not_pf phi) t v
              = Not_pf (substitute_p phi t v). STUB."""
    p.goal(
        "!phi t v. substitute_p (Not_pf phi) t v "
        "          = Not_pf (substitute_p phi t v)",
        types={"phi": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def SUBSTITUTE_P_AT_IMP(p):
    """|- !a b t v.
            substitute_p (Imp_pf a b) t v
              = Imp_pf (substitute_p a t v) (substitute_p b t v). STUB."""
    p.goal(
        "!a b t v. substitute_p (Imp_pf a b) t v "
        "          = Imp_pf (substitute_p a t v) (substitute_p b t v)",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def SUBSTITUTE_P_AT_APP(p):
    """|- !f args t v.
            substitute_p (App_pt f args) t v
              = App_pt f (substitute_p args t v). STUB."""
    p.goal(
        "!f args t v. substitute_p (App_pt f args) t v "
        "             = App_pt f (substitute_p args t v)",
        types={"f": nat0_ty, "args": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Closure under substitute -- preservation of is_pterm / is_pform.
# Same shape as SUBSTITUTE_PRESERVES_IS_FORM in hf_syntax, dropping the
# Forall_f case and its EXCLUDED_MIDDLE on (v = a). Quantifier-free
# substitution is pure structural rewrite, so preservation is uniform
# across constructors.
# ---------------------------------------------------------------------------


@proof
def SUBSTITUTE_P_PRESERVES_IS_PTERM(p):
    """|- !F t v. is_pterm F /\\ is_pterm t ==> is_pterm (substitute_p F t v).
    STUB."""
    p.goal(
        "!F t v. is_pterm F /\\ is_pterm t ==> is_pterm (substitute_p F t v)",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def SUBSTITUTE_P_PRESERVES_IS_PFORM(p):
    """|- !F t v. is_pform F /\\ is_pterm t ==> is_pform (substitute_p F t v).
    STUB."""
    p.goal(
        "!F t v. is_pform F /\\ is_pterm t ==> is_pform (substitute_p F t v)",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


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

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
from nat0_order import define_wf_lt
from hf_syntax import (  # re-exported; PRST uses the same encoding for these
    Empty_t,  # noqa: F401  -- body of Empty_pt
    Var_t,  # noqa: F401  -- body of Var_pt
    Eq_f,  # noqa: F401  -- body of Eq_pf
    Not_f,  # noqa: F401  -- body of Not_pf
    Imp_f,  # noqa: F401  -- body of Imp_pf
    In_a,  # noqa: F401  -- body of In_pa
    VAR_T_AT,  # noqa: F401  -- re-export
    EQ_F_AT,  # noqa: F401  -- re-export
    NOT_F_AT,  # noqa: F401  -- re-export
    IMP_F_AT,  # noqa: F401  -- re-export
    IN_A_AT,  # noqa: F401  -- re-export
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


@proof
def NAT0_LT_APP_PT_L(p):
    """|- !f args. nat0_lt f (App_pt f args). STUB."""
    p.goal("!f args. nat0_lt f (App_pt f args)", types={"f": nat0_ty, "args": nat0_ty})
    p.sorry()


@proof
def NAT0_LT_APP_PT_R(p):
    """|- !f args. nat0_lt args (App_pt f args). STUB."""
    p.goal(
        "!f args. nat0_lt args (App_pt f args)",
        types={"f": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_INJ(p):
    """|- !f1 a1 f2 a2. App_pt f1 a1 = App_pt f2 a2 ==> (f1 = f2 /\\ a1 = a2). STUB."""
    p.goal(
        "!f1 a1 f2 a2. App_pt f1 a1 = App_pt f2 a2 ==> (f1 = f2 /\\ a1 = a2)",
        types={"f1": nat0_ty, "a1": nat0_ty, "f2": nat0_ty, "a2": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_DISJOINT_VAR_T(p):
    """|- !f args v. ~(App_pt f args = Var_t v). STUB."""
    p.goal(
        "!f args v. ~(App_pt f args = Var_t v)",
        types={"f": nat0_ty, "args": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_DISJOINT_EMPTY(p):
    """|- !f args. ~(App_pt f args = Empty_t). STUB."""
    p.goal(
        "!f args. ~(App_pt f args = Empty_t)",
        types={"f": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


@proof
def NAT0_LT_TUP_PT_L(p):
    """|- !a b. nat0_lt a (Tup_pt a b). STUB."""
    p.goal("!a b. nat0_lt a (Tup_pt a b)", types={"a": nat0_ty, "b": nat0_ty})
    p.sorry()


@proof
def NAT0_LT_TUP_PT_R(p):
    """|- !a b. nat0_lt b (Tup_pt a b). STUB."""
    p.goal("!a b. nat0_lt b (Tup_pt a b)", types={"a": nat0_ty, "b": nat0_ty})
    p.sorry()


@proof
def TUP_PT_INJ(p):
    """|- !a1 b1 a2 b2. Tup_pt a1 b1 = Tup_pt a2 b2 ==> (a1 = a2 /\\ b1 = b2). STUB."""
    p.goal(
        "!a1 b1 a2 b2. Tup_pt a1 b1 = Tup_pt a2 b2 ==> (a1 = a2 /\\ b1 = b2)",
        types={"a1": nat0_ty, "b1": nat0_ty, "a2": nat0_ty, "b2": nat0_ty},
    )
    p.sorry()


@proof
def TUP_PT_DISJOINT_VAR_T(p):
    """|- !a b v. ~(Tup_pt a b = Var_t v). STUB."""
    p.goal(
        "!a b v. ~(Tup_pt a b = Var_t v)",
        types={"a": nat0_ty, "b": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def TUP_PT_DISJOINT_EMPTY(p):
    """|- !a b. ~(Tup_pt a b = Empty_t). STUB."""
    p.goal("!a b. ~(Tup_pt a b = Empty_t)", types={"a": nat0_ty, "b": nat0_ty})
    p.sorry()


@proof
def TUP_PT_DISJOINT_APP_PT(p):
    """|- !a b f args. ~(Tup_pt a b = App_pt f args).

    Tag disjointness: Tup_pt has tag 12, App_pt has tag 11. STUB.
    """
    p.goal(
        "!a b f args. ~(Tup_pt a b = App_pt f args)",
        types={"a": nat0_ty, "b": nat0_ty, "f": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


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
              ==> _is_pterm_F f n = _is_pterm_F g n. STUB (Layer 2).
    """
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
    p.sorry()


IS_PTERM_DEF, _IS_PTERM_REC = define_wf_lt(
    "is_pterm",
    parse_type("nat0 -> bool"),
    _IS_PTERM_F,
    IS_PTERM_MONO,
)
is_pterm = mk_const("is_pterm", [])


@proof
def IS_PTERM_AT_EMPTY(p):
    """|- is_pterm Empty_pt. STUB."""
    p.goal("is_pterm Empty_pt")
    p.sorry()


@proof
def IS_PTERM_AT_VAR(p):
    """|- !v. is_pterm (Var_pt v). STUB."""
    p.goal("!v. is_pterm (Var_pt v)", types={"v": nat0_ty})
    p.sorry()


@proof
def IS_PTERM_AT_TUP(p):
    """|- !a b. is_pterm (Tup_pt a b) = (is_pterm a /\\ is_pterm b). STUB."""
    p.goal(
        "!a b. is_pterm (Tup_pt a b) = (is_pterm a /\\ is_pterm b)",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.sorry()


@proof
def IS_PTERM_AT_APP(p):
    """|- !f args. is_pterm (App_pt f args) = (is_pr_sym f /\\ is_pterm args). STUB.

    ``is_pr_sym`` lives in prst_pr. The well-foundedness of the
    recursive call on ``args`` is by NAT0_LT_APP_PT_R.
    """
    p.goal(
        "!f args. is_pterm (App_pt f args) = (is_pr_sym f /\\ is_pterm args)",
        types={"f": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


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
    print("    FREE_IN_P_AT_APP       :", pp_thm(FREE_IN_P_AT_APP))
    print("    SUBSTITUTE_P_AT_TUP    :", pp_thm(SUBSTITUTE_P_AT_TUP))
    print("    SUBSTITUTE_P_AT_APP    :", pp_thm(SUBSTITUTE_P_AT_APP))

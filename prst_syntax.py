# ---------------------------------------------------------------------------
# Stage 1 (PRST) -- syntax of Primitive Recursive Set Theory.
# ---------------------------------------------------------------------------
#
# PRST extends Swierczkowski-style HF by adjoining a *function symbol*
# for every primitive recursive (PR) set function, along with its
# defining recursion equations. The point of the move (vs ``hf_syntax``):
#
#   * In HF, primitive recursive predicates are represented by Sigma_1
#     formulas whose witnesses are explicit *trace sets* (Goedel-Bernays
#     beta function, or in our case ``is_substitute_trace`` plus
#     ``QUOTE_HF`` injectivity). Functions are represented as
#     functional relations; their "evaluation" requires an HF-internal
#     proof that the trace exists and is unique. Substitute alone costs
#     ~600-1000 lines of trace-existence + functionality bookkeeping.
#
#   * In PRST, a PR function ``f`` is a *term constructor*. The PRST
#     term ``App_t f_sym [t1; ...; tk]`` is the value of ``f`` at
#     ``t1, ..., tk``; PRST proves
#         App_t f_sym [t1; ...; tk]  =  <body of f's definition>
#     by direct unfolding (its defining equation is an axiom). No
#     traces, no functionality side proof. Substitute, numeral, diag,
#     Proof_HF all become closed PRST terms with their representability
#     theorems trivial.
#
# Encoding choices:
#
#   Term  ::=  Empty | Var num | Insert Term Term | App f_sym ArgList
#   Form  ::=  Eq Term Term | In Term Term
#           |  Not Form | Imp Form Form | Forall num Form
#
#   ArgList = nat0-encoded list of Terms (cons_l / nil_l from hf_proof).
#
# Tags (extending the HF tag space; preserving HF's existing tags so
# old syntax still parses):
#
#     Empty_pt          :=  0                           (= Empty_t)
#     Var_pt   v        :=  Pair_ord 2 v                (= Var_t v)
#     Eq_pf    t1 t2    :=  Pair_ord 5 (Pair_ord t1 t2) (= Eq_f)
#     Not_pf   F        :=  Pair_ord 6 F                (= Not_f)
#     Imp_pf   F1 F2    :=  Pair_ord 7 (Pair_ord F1 F2) (= Imp_f)
#     Forall_pf n F     :=  Pair_ord 8 (Pair_ord n F)   (= Forall_f)
#     Insert_pt t1 t2   :=  Pair_ord 9 (Pair_ord t1 t2) (= Insert_t)
#     In_pa    t1 t2    :=  Pair_ord 10 (Pair_ord t1 t2)(= In_a)
#     App_pt   f a      :=  Pair_ord 11 (Pair_ord f a)  (NEW)
#
# ``App_pt`` is the only new constructor; the HF ones are re-exported
# under PRST names so downstream PRST formulas can build on existing HF
# syntax lemmas.
#
# Per-function-symbol intro (in ``prst_pr``): each PR function symbol
# ``f`` is a closed nat0 (an id), and ``App_pt f (cons_l t1 ... nil_l)``
# is its application term. The arity and recursion shape of ``f`` is
# pinned by a *defining equation* axiom; ``prst_pr`` introduces a
# uniform recogniser ``is_pr_def`` for those axioms.
#
# All HF structural recognisers (``is_term``, ``is_form``, ``free_in``,
# ``substitute``) are extended with one extra recursion clause for
# ``App_pt``. The clauses are stubbed; their AT-equations follow the
# same shape as the HF ones.
# ---------------------------------------------------------------------------


r"""Syntax of PRST (Primitive Recursive Set Theory) encoded as nat0.

Mirrors ``hf_syntax.py`` and adds the ``App_pt`` constructor for
applications of PR function symbols. See the module-level comment block
for the encoding table.

Stubs: every theorem here is sorried. The expected proof shape is
indicated in each docstring.
"""

from fusion import Var
from basics import mk_const, mk_app
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof, define_with_at
from hf_syntax import (  # re-exported; PRST uses the same encoding for these
    Empty_t,  # noqa: F401  -- body of Empty_pt
    Var_t,  # noqa: F401  -- body of Var_pt
    Eq_f,  # noqa: F401  -- body of Eq_pf
    Not_f,  # noqa: F401  -- body of Not_pf
    Imp_f,  # noqa: F401  -- body of Imp_pf
    Forall_f,  # noqa: F401  -- body of Forall_pf
    Insert_t,  # noqa: F401  -- body of Insert_pt
    In_a,  # noqa: F401  -- body of In_pa
    VAR_T_AT,  # noqa: F401  -- re-export
    EQ_F_AT,  # noqa: F401  -- re-export
    NOT_F_AT,  # noqa: F401  -- re-export
    IMP_F_AT,  # noqa: F401  -- re-export
    FORALL_F_AT,  # noqa: F401  -- re-export
    INSERT_T_AT,  # noqa: F401  -- re-export
    IN_A_AT,  # noqa: F401  -- re-export
)


# ---------------------------------------------------------------------------
# Stage 1 (a) -- PRST renames for HF constructors.
#
# PRST inherits HF's term/form constructors verbatim. Each PRST name
# is defined as an alias of the corresponding HF constant so that
# downstream parse-strings can refer to ``Var_pt`` etc.
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

FORALL_PF_DEF = define(
    "Forall_pf", parse_type("nat0 -> nat0 -> nat0"), "Forall_f"
)
Forall_pf = mk_const("Forall_pf", [])

INSERT_PT_DEF = define(
    "Insert_pt", parse_type("nat0 -> nat0 -> nat0"), "Insert_t"
)
Insert_pt = mk_const("Insert_pt", [])

IN_PA_DEF = define("In_pa", parse_type("nat0 -> nat0 -> nat0"), "In_a")
In_pa = mk_const("In_pa", [])


# ---------------------------------------------------------------------------
# Stage 1 (b) -- App_pt: the new term constructor for PR-function
# applications.
#
#     App_pt f args  :=  Pair_ord 11 (Pair_ord f args)
#
# ``f`` is the godelnum of a PR-function symbol (a closed nat0 chosen
# in ``prst_pr``); ``args`` is a cons_l-encoded list of term godelnums.
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


# ---------------------------------------------------------------------------
# Stage 1 (c) -- size and injectivity lemmas for App_pt.
#
# Same shape as NAT0_LT_INSERT_T_L / _R and the constructor-INJ lemmas
# in hf_syntax. Proofs: one or two applications of NAT0_LT_PAIR_ORD_L /
# _R chained via NAT0_LT_TRANS for size; PAIR_ORD_INJ at slots 0/1 for
# injectivity.
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
    """|- !f args v. ~(App_pt f args = Var_t v).

    Tag disjointness: App_pt tag = SUC0^11 0 vs Var_t tag = SUC0^2 0.
    STUB.
    """
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
def APP_PT_DISJOINT_INSERT_T(p):
    """|- !f args t1 t2. ~(App_pt f args = Insert_t t1 t2). STUB."""
    p.goal(
        "!f args t1 t2. ~(App_pt f args = Insert_t t1 t2)",
        types={
            "f": nat0_ty,
            "args": nat0_ty,
            "t1": nat0_ty,
            "t2": nat0_ty,
        },
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 1 (d) -- is_term recogniser extended with App_pt.
#
# is_pterm t  iff t is a well-formed PRST term, i.e. either:
#   * Empty_pt
#   * Var_pt v for some v
#   * Insert_pt t1 t2 with t1, t2 is_pterm
#   * App_pt f args where f is a registered PR function symbol id and
#     ``args`` is a cons_l-encoded list whose every entry is_pterm and
#     whose length matches f's declared arity.
#
# The "registered function symbol id" predicate (``is_pr_sym``) lives in
# ``prst_pr``. ``is_pterm`` is well-founded recursive on nat0_lt; the
# App_pt case calls back into is_pterm on each list entry, justified by
# NAT0_LT_APP_PT_R + cons_l size lemmas in hf_proof.
#
# AT-equations: stubbed; same shape as IS_TERM_AT_* in hf_syntax.
# ---------------------------------------------------------------------------


# is_pterm : nat0 -> bool   (well-founded recursion on nat0_lt; stub body)
IS_PTERM_DEF = define("is_pterm", parse_type("nat0 -> bool"), "\\t:nat0. T")
is_pterm = mk_const("is_pterm", [])

# Helper stubs referenced in IS_PTERM_AT_APP / FREE_IN_P_AT_APP /
# SUBSTITUTE_P_AT_APP. Real definitions would walk the cons_l list of
# argument terms. Posted here with dummy bodies so the sketch parses.
ALL_PTERM_DEF = define("all_pterm", parse_type("nat0 -> bool"), "\\args:nat0. T")
all_pterm = mk_const("all_pterm", [])

LIST_LENGTH_DEF = define(
    "list_length", parse_type("nat0 -> nat0"), "\\l:nat0. l"
)
list_length = mk_const("list_length", [])

ANY_FREE_IN_P_DEF = define(
    "any_free_in_p",
    parse_type("nat0 -> nat0 -> bool"),
    "\\args:nat0. \\v:nat0. F",
)
any_free_in_p = mk_const("any_free_in_p", [])

MAP_SUBSTITUTE_P_DEF = define(
    "map_substitute_p",
    parse_type("nat0 -> nat0 -> nat0 -> nat0"),
    "\\args:nat0. \\t:nat0. \\v:nat0. args",
)
map_substitute_p = mk_const("map_substitute_p", [])

# is_pr_sym / pr_arity belong semantically to prst_pr, but the
# is_pterm AT-equation here references them, so they need to exist
# at parser level by the time prst_syntax loads. Registered here as
# placeholders; prst_pr uses these same names.
IS_PR_SYM_DEF = define("is_pr_sym", parse_type("nat0 -> bool"), "\\f:nat0. F")
is_pr_sym = mk_const("is_pr_sym", [])

PR_ARITY_DEF = define("pr_arity", parse_type("nat0 -> nat0"), "\\f:nat0. 0")
pr_arity = mk_const("pr_arity", [])


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
def IS_PTERM_AT_INSERT(p):
    """|- !t1 t2. is_pterm (Insert_pt t1 t2)
                 = (is_pterm t1 /\\ is_pterm t2). STUB."""
    p.goal(
        "!t1 t2. is_pterm (Insert_pt t1 t2) = (is_pterm t1 /\\ is_pterm t2)",
        types={"t1": nat0_ty, "t2": nat0_ty},
    )
    p.sorry()


@proof
def IS_PTERM_AT_APP(p):
    """|- !f args. is_pterm (App_pt f args)
                  = (is_pr_sym f /\\ pr_arity f = list_length args
                                  /\\ all_pterm args). STUB.

    ``is_pr_sym``, ``pr_arity``, ``all_pterm`` live in prst_pr. The
    well-foundedness justification for the recursive call inside
    ``all_pterm`` uses NAT0_LT_APP_PT_R chained with cons_l size lemmas.
    """
    p.goal(
        "!f args. is_pterm (App_pt f args) "
        "         = (is_pr_sym f "
        "            /\\ pr_arity f = list_length args "
        "            /\\ all_pterm args)",
        types={"f": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 1 (e) -- is_form recogniser.
#
# Identical to is_form for HF except every atom recognises is_pterm
# (not is_term) in its term slots, picking up App_pt automatically.
# ---------------------------------------------------------------------------


IS_PFORM_DEF = define("is_pform", parse_type("nat0 -> bool"), "\\phi:nat0. T")
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


@proof
def IS_PFORM_AT_FORALL(p):
    """|- !v F. is_pform (Forall_pf v F) = is_pform F. STUB."""
    p.goal(
        "!v F. is_pform (Forall_pf v F) = is_pform F",
        types={"v": nat0_ty, "F": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 1 (f) -- free_in extended for App_pt.
#
# free_in_p (App_pt f args) v   iff  free_in_p (some entry of args) v.
#
# ---------------------------------------------------------------------------


FREE_IN_P_DEF = define(
    "free_in_p", parse_type("nat0 -> nat0 -> bool"), "\\phi:nat0. \\v:nat0. F"
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
def FREE_IN_P_AT_APP(p):
    """|- !f args v. free_in_p (App_pt f args) v = any_free_in_p args v.

    Where ``any_free_in_p args v`` walks the cons_l list and ORs
    ``free_in_p`` over each entry. STUB.
    """
    p.goal(
        "!f args v. free_in_p (App_pt f args) v = any_free_in_p args v",
        types={"f": nat0_ty, "args": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 1 (g) -- substitute extended for App_pt.
#
# substitute_p (App_pt f args) t v
#     = App_pt f (map_substitute_p args t v).
#
# I.e. substitution distributes pointwise across the argument list. No
# capture issues because App_pt does not bind variables.
# ---------------------------------------------------------------------------


SUBSTITUTE_P_DEF = define(
    "substitute_p",
    parse_type("nat0 -> nat0 -> nat0 -> nat0"),
    "\\phi:nat0. \\t:nat0. \\v:nat0. phi",
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
def SUBSTITUTE_P_AT_APP(p):
    """|- !f args t v.
            substitute_p (App_pt f args) t v
              = App_pt f (map_substitute_p args t v). STUB."""
    p.goal(
        "!f args t v. substitute_p (App_pt f args) t v "
        "             = App_pt f (map_substitute_p args t v)",
        types={"f": nat0_ty, "args": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Closure under substitute -- preservation of is_pterm / is_pform.
# Same shape as SUBSTITUTE_PRESERVES_IS_FORM in hf_syntax, extended
# with the App_pt clause (which is closed under substitute by the
# above AT-equation plus the map_substitute_p preservation lemma).
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
# Notes on the size of this module vs hf_syntax.py.
#
# hf_syntax.py is ~3500 lines. prst_syntax.py mostly *re-exports* HF
# constructors plus adds the App_pt clause; the new content is:
#
#   * App_pt itself (one constructor + 4 size/inj lemmas).
#   * One extra clause in each of is_term, is_form, free_in, substitute
#     (4 AT-equations + 2 preservation lemmas).
#
# Estimate ~500 lines once filled in -- the bulk of HF's syntax lemmas
# (Pair_ord injectivity, the disjointness chain across all 8 HF tags,
# substitute distributing over Imp/Forall/Eq/In, free_in computing
# correctly) is inherited verbatim and only needs re-stating, not
# re-proving.
# ---------------------------------------------------------------------------


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 1 (PRST) -- syntax.")
    print("    APP_PT_DEF             :", pp_thm(APP_PT_DEF))
    print("    NAT0_LT_APP_PT_L       :", pp_thm(NAT0_LT_APP_PT_L))
    print("    NAT0_LT_APP_PT_R       :", pp_thm(NAT0_LT_APP_PT_R))
    print("    APP_PT_INJ             :", pp_thm(APP_PT_INJ))
    print("    IS_PTERM_AT_APP        :", pp_thm(IS_PTERM_AT_APP))
    print("    FREE_IN_P_AT_APP       :", pp_thm(FREE_IN_P_AT_APP))
    print("    SUBSTITUTE_P_AT_APP    :", pp_thm(SUBSTITUTE_P_AT_APP))

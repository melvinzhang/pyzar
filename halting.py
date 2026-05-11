"""Undecidability of the halting problem, via SK combinators over HF.

SKETCH ONLY -- this file lays out the construction; the proofs are
stubbed with ``p.sorry()``. The goal is to state and prove, as a HOL
theorem, that no SK combinator decides whether an SK term has a normal
form:

    |- ~ ?H. is_sk_term H /\\
             !t. is_sk_term t ==> ((App H t) reduces_to K_t  <=>  halts t).

The whole development lives over ``hf_sets.py`` plus ``nat0.py``.
Axiomatic cost: zero. The construction reuses ``Pair_ord`` for tagged
HF tuples; no new primitives.

------------------------------------------------------------------
Why SK and not Turing machines or lambda
------------------------------------------------------------------

Three computation models give the same theorem; SK is the cheapest:

  TM        : finite tuple <Q, Sigma, delta, q0, F> + tape encoding +
              configuration step + universal machine. ~600 LOC.
  lambda    : Var/Lam/App + de Bruijn shift + capture-free substitution
              + beta-step. ~500 LOC. Substitution interacts with the
              bit-encoded canonical-form preconditions of ``substitute``
              (cf. ``project_pyzar_simp_select_constraint``).
  SK        : three tags, no binders, two local rewrite rules.
              ~300 LOC. No substitution lemmas. ``Omega = SII(SII)``
              is the non-halting witness, definable in five symbols.

The diagonal is the same shape in all three. SK wins by avoiding the
nastiest infrastructure piece (substitution under binders) while
keeping the diagonal mechanically identical.

------------------------------------------------------------------
The idea (Turing 1936; SK presentation: Barendregt Ch. 7)
------------------------------------------------------------------

Three ingredients:

  (1) *Encoding.* SK terms are finite ternary trees: leaves S/K, internal
      nodes App. Each is a tagged HF tuple, hence a nat0. Reduction
      rules ``K x y -> x`` and ``S x y z -> x z (y z)`` are local
      pattern matches.

  (2) *Halting.*  ``halts t := ?n u. reduces_in n t u /\\ is_normal u``.
      Existential over ``num`` plus a primitive recursive body, so
      ``halts`` is r.e. -- but not, the theorem says, decidable by an
      SK term.

  (3) *Diagonal.* Curry's fixed-point combinator ``Y`` gives, for any
      ``f``, a term ``Y f`` such that ``Y f -->* f (Y f)``. Apply with
      ``f := \\x. if H(x) then Omega else K_t``. The fixed point ``d``
      satisfies ``d -->* if H(d) then Omega else K_t``. If ``H`` decides
      halting, ``halts d <=> halts (if H(d) then Omega else K_t) <=>
      halts d`` -- contradiction either way.

Lambda-abstraction is *defined* on SK (Curry's algorithm ``[x] e``);
no binder primitive needed.

------------------------------------------------------------------
The HOL encoding hurdle
------------------------------------------------------------------

There isn't one for the data: ``Pair_ord`` from ``hf_sets.py`` gives
ordered pairs on nat0, so tagged tuples ``<n, t1, ..., tk>`` are
nested Pair_ord's. The work is:

  * Defining ``sk_step`` as a primitive recursive HF function (it
    inspects the head of an application chain and matches K/S).
  * Defining ``sk_reduces : num -> nat0 -> nat0 -> bool`` by primitive
    recursion on the step count, and ``halts`` as the existential
    closure.
  * Constructing ``Y`` and proving its fixed-point property as an SK
    reduction.
  * The diagonal argument itself -- once the reduction lemmas are in
    place, ~30 lines.

------------------------------------------------------------------
Stage map
------------------------------------------------------------------

  Stage 0:  SK terms as tagged HF tuples (S_t, K_t, App_t, is_sk_term).
  Stage 1:  One-step reduction sk_step + determinism.
  Stage 2:  Multi-step sk_reduces, normal-form predicate, halts.
  Stage 3:  Useful combinators: I, KI, Omega; OMEGA_NON_HALTING.
  Stage 4:  Curry's fixed-point combinator Y and the fixed-point
            theorem Y_FIXED_POINT.
  Stage 5:  Lambda-abstraction emulation [x]e (the bracket abstraction
            algorithm) -- used only to define D readably; could be
            inlined.
  Stage 6:  HALTING_UNDECIDABLE: no SK term decides halting.
  Stage 7:  Corollary: ``halts`` is not primitive recursive
            (essentially, the standard Rice-flavoured consequence).

------------------------------------------------------------------
What this gives and doesn't give
------------------------------------------------------------------

Derived from the bare HOL kernel + ``hf_sets.py``:
  * Undecidability of halting for SK combinators (the headline).
  * Non-haltingness of Omega -- a concrete non-terminating program.
  * SK is Turing-complete in the weak sense: Y gives general recursion.

Not in scope here:
  * Equivalence with Turing machines or lambda calculus (would need a
    third file). The theorem stands on its own without it.
  * Church-Rosser confluence. Cleanly provable here via the standard
    parallel-reduction argument (Tait/Martin-Loef minus the binder
    cases, so ~80 lines), but the halting theorem does not depend on
    it.

Pairs especially well with ``godel_first.py``: the diagonal in this
file is mechanically the same as the Goedel diagonal -- self-application
producing self-reference. Tarski's undefinability of truth is the same
diagonal a third time.
"""

from fusion import Var, new_constant
from basics import mk_const, mk_app, mk_abs
from parser import define, parse_type, add_const
from nat0 import nat0_ty, ZERO, mk_suc0
from proof import proof
from hf_sets import Pair_ord


# ---------------------------------------------------------------------------
# Stage 0 -- SK terms as tagged HF tuples.
#
#   S_t   := Pair_ord 0 0
#   K_t   := Pair_ord (SUC0 0) 0
#   App_t := \\t u. Pair_ord (SUC0 (SUC0 0)) (Pair_ord t u)
#
# A nat0 ``t`` is a well-formed SK term iff it lies in the inductive
# closure of {S_t, K_t} under App_t.  The predicate ``is_sk_term`` is
# primitive recursive on the structural decoder for Pair_ord (each
# unfolding strictly reduces the nat0 by Foundation, so HF1-5 give
# termination).
# ---------------------------------------------------------------------------


_tag_S = ZERO
_tag_K = mk_suc0(ZERO)
_tag_App = mk_suc0(mk_suc0(ZERO))


S_T_DEF = define(
    "S_t",
    nat0_ty,
    mk_app(Pair_ord, _tag_S, ZERO),
)
S_t = mk_const("S_t", [])


K_T_DEF = define(
    "K_t",
    nat0_ty,
    mk_app(Pair_ord, _tag_K, ZERO),
)
K_t = mk_const("K_t", [])


_t_n0 = Var("t", nat0_ty)
_u_n0 = Var("u", nat0_ty)


APP_T_DEF = define(
    "App_t",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(
        _t_n0,
        mk_abs(
            _u_n0,
            mk_app(Pair_ord, _tag_App, mk_app(Pair_ord, _t_n0, _u_n0)),
        ),
    ),
)
App_t = mk_const("App_t", [])


# ``is_sk_term`` is the recursive predicate
#   is_sk_term t  :=  t = S_t \/ t = K_t \/
#                     (?a b. t = App_t a b /\ is_sk_term a /\ is_sk_term b).
# Defined by well-founded recursion on the Pair_ord-depth of t (each
# subterm is strictly smaller in nat0_lt via the bit-encoding).
new_constant("is_sk_term", parse_type("nat0 -> bool"))
is_sk_term = mk_const("is_sk_term", [])
add_const("is_sk_term", is_sk_term)


@proof
def IS_SK_TERM_S(p):
    """|- is_sk_term S_t.  Recursion base case."""
    p.goal("is_sk_term S_t")
    p.sorry()


@proof
def IS_SK_TERM_K(p):
    """|- is_sk_term K_t."""
    p.goal("is_sk_term K_t")
    p.sorry()


@proof
def IS_SK_TERM_APP(p):
    """|- !a b. is_sk_term a /\\ is_sk_term b ==> is_sk_term (App_t a b)."""
    p.goal("!a b. is_sk_term a /\\ is_sk_term b ==> is_sk_term (App_t a b)")
    p.sorry()


@proof
def IS_SK_TERM_CASES(p):
    """|- !t. is_sk_term t <=>
              t = S_t \\/ t = K_t \\/
              ?a b. t = App_t a b /\\ is_sk_term a /\\ is_sk_term b.

    Recursion equation, used for structural induction on SK terms.
    Discharges via the Pair_ord depth measure plus HF Foundation.
    """
    p.goal(
        "!t. is_sk_term t = "
        "    (t = S_t \\/ t = K_t \\/ "
        "     (?a b. t = App_t a b /\\ is_sk_term a /\\ is_sk_term b))"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 1 -- one-step reduction.
#
# Strategy: leftmost-outermost (call-by-name).  Deterministic, hence
# ``sk_step`` is a *function* nat0 -> nat0 rather than a relation; for
# normal forms it returns the term itself, and the predicate
# ``is_normal`` distinguishes the two cases.
#
# Reduction rules:
#   sk_step (App_t (App_t K_t x) y)              = x
#   sk_step (App_t (App_t (App_t S_t x) y) z)    = App_t (App_t x z) (App_t y z)
#   otherwise (head of leftmost spine is a free variable / S short of
#   arity / K short of arity):  recurse into the left child.
#
# The K/S patterns are decidable by inspecting the spine, which is a
# left-fold over App_t.  Primitive recursive on the Pair_ord depth.
# ---------------------------------------------------------------------------


new_constant("sk_step", parse_type("nat0 -> nat0"))
sk_step = mk_const("sk_step", [])
add_const("sk_step", sk_step)


new_constant("is_normal", parse_type("nat0 -> bool"))
is_normal = mk_const("is_normal", [])
add_const("is_normal", is_normal)


@proof
def SK_STEP_K(p):
    """|- !x y. sk_step (App_t (App_t K_t x) y) = x."""
    p.goal("!x y. sk_step (App_t (App_t K_t x) y) = x")
    p.sorry()


@proof
def SK_STEP_S(p):
    """|- !x y z. sk_step (App_t (App_t (App_t S_t x) y) z)
                  = App_t (App_t x z) (App_t y z)."""
    p.goal(
        "!x y z. sk_step (App_t (App_t (App_t S_t x) y) z) "
        "         = App_t (App_t x z) (App_t y z)"
    )
    p.sorry()


@proof
def IS_NORMAL_S(p):
    """|- is_normal S_t."""
    p.goal("is_normal S_t")
    p.sorry()


@proof
def IS_NORMAL_K(p):
    """|- is_normal K_t."""
    p.goal("is_normal K_t")
    p.sorry()


@proof
def IS_NORMAL_CASES(p):
    """|- !t. is_sk_term t ==>
              (is_normal t <=> sk_step t = t).

    A leftmost-outermost step is the identity exactly on normal forms.
    Used to phrase ``halts`` as the existence of a step count after
    which iteration stabilises.
    """
    p.goal("!t. is_sk_term t ==> (is_normal t = (sk_step t = t))")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2 -- multi-step reduction and halting.
#
#   sk_iter 0 t       = t
#   sk_iter (SUC n) t = sk_step (sk_iter n t)
#
#   reduces_in n t u  :=  sk_iter n t = u
#   halts t           :=  ?n. is_normal (sk_iter n t)
#
# ``halts`` is therefore a Sigma_1 predicate over nat0: r.e., not
# (we will show) recursive in the SK sense.
# ---------------------------------------------------------------------------


new_constant("sk_iter", parse_type("nat0 -> nat0 -> nat0"))
sk_iter = mk_const("sk_iter", [])
add_const("sk_iter", sk_iter)


#   halts t  :=  ?n. is_normal (sk_iter n t).
# Posted via ``new_constant`` for now; the real ``define`` reads
#   "\\t:nat0. ?n:nat0. is_normal (sk_iter n t)"
# and is a one-liner once ``sk_iter`` and ``is_normal`` are in place.
new_constant("halts", parse_type("nat0 -> bool"))
halts = mk_const("halts", [])
add_const("halts", halts)


@proof
def SK_ITER_ZERO(p):
    """|- !t. sk_iter 0 t = t."""
    p.goal("!t. sk_iter 0 t = t")
    p.sorry()


@proof
def SK_ITER_SUC(p):
    """|- !n t. sk_iter (SUC0 n) t = sk_step (sk_iter n t)."""
    p.goal("!n t. sk_iter (SUC0 n) t = sk_step (sk_iter n t)")
    p.sorry()


@proof
def HALTS_AT(p):
    """|- !t. halts t <=> ?n. is_normal (sk_iter n t).

    Restating ``HALTS_DEF`` as the standard Sigma_1 predicate.  The
    canonical-form work goes here.
    """
    p.goal("!t. halts t = (?n. is_normal (sk_iter n t))")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 3 -- the standard combinators.
#
#   I_t  := App_t (App_t S_t K_t) K_t           -- identity
#   KI_t := App_t K_t I_t                       -- "false" Church bool
#   D_t  := App_t S_t (App_t I_t I_t)           -- self-duplicator (Curry)
#   Omega_t := App_t D_t D_t                    -- canonical loop
#
# Reductions:
#   I_t x   -->  x                              (S K K x --> K x (K x) --> x)
#   Omega_t -->  Omega_t                        (one-step self-loop)
#
# Hence Omega_t never reaches a normal form: every ``sk_iter n Omega_t``
# equals Omega_t.
# ---------------------------------------------------------------------------


I_T_DEF = define(
    "I_t",
    nat0_ty,
    mk_app(App_t, mk_app(App_t, S_t, K_t), K_t),
)
I_t = mk_const("I_t", [])


KI_T_DEF = define(
    "KI_t",
    nat0_ty,
    mk_app(App_t, K_t, I_t),
)
KI_t = mk_const("KI_t", [])


# D_t := S I I  -- the self-applicator
_D_self_t = mk_app(App_t, mk_app(App_t, S_t, I_t), I_t)


OMEGA_T_DEF = define(
    "Omega_t",
    nat0_ty,
    mk_app(App_t, _D_self_t, _D_self_t),
)
Omega_t = mk_const("Omega_t", [])


@proof
def I_T_REDUCES(p):
    """|- !x. is_sk_term x ==> sk_iter (SUC0 (SUC0 0)) (App_t I_t x) = x.

    I = SKK; SKK x reduces in two steps to x (one for S, one to drop the
    spurious K-redex).
    """
    p.goal("!x. is_sk_term x ==> sk_iter (SUC0 (SUC0 0)) (App_t I_t x) = x")
    p.sorry()


@proof
def OMEGA_T_SELF_LOOP(p):
    """|- sk_step Omega_t = Omega_t.

    Proof:  Omega_t = App (S I I) (S I I)
                  --> App (App I (S I I)) (App I (S I I))   (S-rule)
                  -->* (S I I) (S I I)
                   = Omega_t.

    The "-->*" hides two I-reductions; for the leftmost-outermost step
    we land back at Omega_t after exactly three steps, so the cleaner
    invariant is ``sk_iter 3 Omega_t = Omega_t``.  Either form is fine
    for OMEGA_NON_HALTING; we pick whichever matches sk_step's
    definition.
    """
    p.goal("sk_step Omega_t = Omega_t")
    p.sorry()


@proof
def OMEGA_NON_HALTING(p):
    """|- ~ halts Omega_t.

    From OMEGA_T_SELF_LOOP by induction on the step count:
    sk_iter n Omega_t = Omega_t for every n, and Omega_t is not normal
    (its head spine has an active S-redex).
    """
    p.goal("~ halts Omega_t")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 4 -- Curry's fixed-point combinator.
#
#   Y_t := App_t L_t L_t      where    L_t := App_t S_t (App_t S_t K_t)
#                                              applied to itself appropriately;
#                                              see e.g. Barendregt Def. 6.1.3.
#
# Concretely the standard SK-encoding is
#   Y := S S K (S (K (S S (S (S S K)))) K)
# or any other Y-witness; the specific shape doesn't matter, only the
# fixed-point equation.
#
# The fixed-point theorem:
#   |- !f. is_sk_term f ==>
#          ?n. sk_iter n (App_t Y_t f) = App_t f (App_t Y_t f).
#
# i.e. ``Y f`` reduces in finitely many steps to ``f (Y f)``.  This is
# all we need from Y for the diagonal.
# ---------------------------------------------------------------------------


new_constant("Y_t", nat0_ty)
Y_t = mk_const("Y_t", [])


@proof
def IS_SK_TERM_Y(p):
    """|- is_sk_term Y_t.

    Y_t is a fixed concrete SK term; ``is_sk_term`` follows by
    repeated application of IS_SK_TERM_S/K/APP.
    """
    p.goal("is_sk_term Y_t")
    p.sorry()


@proof
def Y_FIXED_POINT(p):
    """|- !f. is_sk_term f ==>
              ?n. sk_iter n (App_t Y_t f) = App_t f (App_t Y_t f).

    Curry's fixed-point theorem in SK.  Discharges by unfolding Y_t's
    concrete encoding and computing the reduction explicitly (~5
    sk_step's, all K/S rule applications).
    """
    p.goal(
        "!f. is_sk_term f ==> "
        "    ?n. sk_iter n (App_t Y_t f) = App_t f (App_t Y_t f)"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 5 -- bracket abstraction (Curry's [x] e).
#
# We need a constant ``flip_t`` that, applied to a Church-bool b and two
# values a/c, returns ``a`` if b = K_t (true) and ``c`` if b = KI_t
# (false).  Standard encoding:
#
#   flip_t b a c  :=  b a c       (if Church booleans are K_t and KI_t,
#                                  then K_t a c -->* a and KI_t a c -->* c)
#
# Hence flip_t is just I_t.  We expose it as a named constant only to
# make the diagonal construction readable.
#
# This stage is bookkeeping; could be inlined.
# ---------------------------------------------------------------------------


@proof
def CHURCH_TRUE_REDUCES(p):
    """|- !a c. is_sk_term a /\\ is_sk_term c ==>
                ?n. sk_iter n (App_t (App_t K_t a) c) = a.

    K_t a c -->* a, i.e. the "true" Church bool selects its first arg.
    """
    p.goal(
        "!a c. is_sk_term a /\\ is_sk_term c ==> "
        "      ?n. sk_iter n (App_t (App_t K_t a) c) = a"
    )
    p.sorry()


@proof
def CHURCH_FALSE_REDUCES(p):
    """|- !a c. is_sk_term a /\\ is_sk_term c ==>
                ?n. sk_iter n (App_t (App_t KI_t a) c) = c.

    KI_t a c = K I a c -->* I c -->* c.
    """
    p.goal(
        "!a c. is_sk_term a /\\ is_sk_term c ==> "
        "      ?n. sk_iter n (App_t (App_t KI_t a) c) = c"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 6 -- the diagonal.
#
# Assume for contradiction that some SK term H decides halting in the
# sense that, for every closed term t,
#
#       App_t H t  -->*  K_t       if halts t
#       App_t H t  -->*  KI_t      if ~halts t.
#
# (Bool-output, leftmost-outermost.)  Define
#
#       f := \\x. (H x) Omega_t K_t              -- bracket-abstracted
#       d := Y_t f                               -- fixed point of f
#
# Then ``d -->* f d -->* (H d) Omega_t K_t``.  Case split:
#   * If halts d: H d -->* K_t, so d -->* K_t a c -->* Omega_t,
#     and halts d implies halts Omega_t -- contradicting
#     OMEGA_NON_HALTING.
#   * If ~halts d: H d -->* KI_t, so d -->* KI_t a c -->* K_t, which
#     is normal -- so halts d, contradicting the assumption.
#
# Either way contradiction; hence no such H exists.
# ---------------------------------------------------------------------------


# ``halts_decider H`` says H is an SK term that decides halting via the
# K_t / KI_t output convention.
new_constant("halts_decider", parse_type("nat0 -> bool"))
halts_decider = mk_const("halts_decider", [])
add_const("halts_decider", halts_decider)


@proof
def HALTS_DECIDER_DEF_THM(p):
    """|- !H. halts_decider H <=>
              is_sk_term H /\\
              !t. is_sk_term t ==>
                  (halts t  ==> ?n. sk_iter n (App_t H t) = K_t) /\\
                  (~halts t ==> ?n. sk_iter n (App_t H t) = KI_t).

    Characterisation of ``halts_decider``.  This is the *definition*
    expanded; once we drop the ``new_constant`` placeholder and write
    a real ``define``, this becomes a one-liner.
    """
    p.goal(
        "!H. halts_decider H = "
        "    (is_sk_term H /\\ "
        "     !t. is_sk_term t ==> "
        "         (halts t ==> (?n. sk_iter n (App_t H t) = K_t)) /\\ "
        "         (~halts t ==> (?n. sk_iter n (App_t H t) = KI_t)))"
    )
    p.sorry()


@proof
def HALTING_REDUCTION_PRESERVED(p):
    """|- !t u n. is_sk_term t /\\ sk_iter n t = u ==> (halts t <=> halts u).

    Halting is invariant under reduction: prepending finitely many
    steps doesn't change whether a normal form is reachable.  Needed
    in both branches of the diagonal contradiction to push ``halts``
    through ``-->*``.
    """
    p.goal(
        "!t u n. is_sk_term t /\\ sk_iter n t = u ==> "
        "        (halts t = halts u)"
    )
    p.sorry()


@proof
def HALTING_UNDECIDABLE(p):
    """|- ~ ?H. halts_decider H.

    THE THEOREM.  No SK combinator decides halting.

    Proof (the diagonal sketched above):

      Assume H with halts_decider H.  Build
        f := an SK term satisfying  App_t f x -->* App_t (App_t (App_t H x)
                                                            Omega_t) K_t
             for all x   (via bracket abstraction on x).
        d := App_t Y_t f.

      By Y_FIXED_POINT:  d -->* App_t f d
                            -->* App_t (App_t (App_t H d) Omega_t) K_t.

      Case 1.  halts d.
        Then App_t H d -->* K_t (decider hypothesis), so
          d -->* App_t (App_t K_t Omega_t) K_t -->* Omega_t
        (by CHURCH_TRUE_REDUCES).  By HALTING_REDUCTION_PRESERVED,
        halts Omega_t -- contradicting OMEGA_NON_HALTING.

      Case 2.  ~halts d.
        Then App_t H d -->* KI_t, so
          d -->* App_t (App_t KI_t Omega_t) K_t -->* K_t
        (by CHURCH_FALSE_REDUCES).  K_t is normal (IS_NORMAL_K), so
        halts d via HALTING_REDUCTION_PRESERVED -- contradicting
        the case hypothesis.

      Either branch contradicts; hence no such H.
    """
    p.goal("~ (?H. halts_decider H)")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 7 -- corollaries.
# ---------------------------------------------------------------------------


@proof
def HALTS_NOT_SK_REPRESENTABLE(p):
    """|- ~ ?H. is_sk_term H /\\
                !t. is_sk_term t ==>
                    (halts t  ==> ?n. sk_iter n (App_t H t) = K_t) /\\
                    (~halts t ==> ?n. sk_iter n (App_t H t) = KI_t).

    HALTING_UNDECIDABLE, restated as non-existence of an SK term
    computing the characteristic function of ``halts``.  Immediate
    from HALTING_UNDECIDABLE + HALTS_DECIDER_DEF_THM.
    """
    p.goal(
        "~ (?H. is_sk_term H /\\ "
        "       !t. is_sk_term t ==> "
        "           (halts t ==> (?n. sk_iter n (App_t H t) = K_t)) /\\ "
        "           (~halts t ==> (?n. sk_iter n (App_t H t) = KI_t)))"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Estimated line budget (once stubs are discharged):
#
#   Stage 0 (SK terms + is_sk_term)          : ~50  lines
#   Stage 1 (sk_step + is_normal)            : ~80  lines (spine analysis)
#   Stage 2 (sk_iter + halts)                : ~30  lines
#   Stage 3 (I, KI, Omega + OMEGA_NON_HALT)  : ~40  lines
#   Stage 4 (Y + fixed-point thm)            : ~30  lines
#   Stage 5 (Church-bool selectors)          : ~20  lines
#   Stage 6 (diagonal + HALTING_UNDECIDABLE) : ~50  lines
#   Stage 7 (corollaries)                    : ~10  lines
#   -----------------------------------------------------
#   Total                                    : ~310 lines
#
# Comparison: Norrish's HOL4 ``lambdaTheory`` halting development is
# ~2k lines because it carries the lambda-calculus substitution
# infrastructure.  Replacing lambda with SK removes that piece outright;
# the diagonal portion is the same size.
# ---------------------------------------------------------------------------

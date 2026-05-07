"""Eudoxus / Schanuel--Arthan construction of the real numbers.

SKETCH ONLY -- this file lays out the construction; the proofs are
stubbed with strategy comments rather than executed. The goal is to
build the ordered field of reals as a *defined* type over the existing
``int`` layer, *without* going through Dedekind cuts or Cauchy
sequences. Net cost: zero new axioms, no countable choice, no power
set, no sets-of-rationals.

------------------------------------------------------------------
The idea (Schanuel 1985; Arthan, "The Eudoxus Real Numbers" 2004)
------------------------------------------------------------------

An *almost homomorphism* (Arthan's "slope") is a function f : Z -> Z
whose additive defect

    B(f)  :=  { f(m + n) - f(m) - f(n)  |  m, n in Z }

is a *bounded* subset of Z. Two slopes are equivalent when their
difference is bounded:

    f ~ g  <=>  { f(n) - g(n) | n in Z }  is bounded.

The reals are the quotient

    R  :=  { f : Z -> Z | f is a slope }  /  ~

with operations

    [f] + [g]    :=  [n |-> f n + g n]
    [f] * [g]    :=  [f o g]                       -- composition!
    -[f]         :=  [n |-> -(f n)]
    0            :=  [n |-> 0]
    1            :=  [n |-> n]                     -- identity
    [f] > 0      :<=>  ~(f bounded above by some constant on N+)
                                                   -- equivalently:
                                                       eventually
                                                       f n > C for all C
    Z -> R       :    q  |->  [n |-> q * n]

and that is the entire construction. Field axioms, total order,
Archimedean property, and Dedekind completeness all fall out of
elementary inequalities about slopes -- no rationals, no Cauchy
sequences, no countable choice, no power set.

The killer feature is multiplication. With Cauchy sequences,
multiplication needs a uniform-Cauchy argument and a choice of bound;
with Dedekind cuts, multiplication needs four-way case splits on signs.
Here multiplication is *function composition* and associativity of
multiplication is associativity of ``o``.

------------------------------------------------------------------
What this replaces
------------------------------------------------------------------

In the Landau roadmap, Chapter 4 introduces the reals via Dedekind cuts
of rationals. A faithful pyzar port of that chapter would need:

  * A type ``rat -> bool`` for cuts (no separate set type yet exists),
  * Predicates encoding "downward closed", "no max", "non-trivial",
  * A subtype carve-out of ``rat -> bool`` by the cut predicate,
  * Lifted ordering, addition, and multiplication (the last with
    sign case splits),
  * A completeness proof that takes the cut union of a bounded family.

That is roughly the size of ``rat_int.py`` plus ``frac.py`` combined.

The Eudoxus alternative skips ``frac.py``, ``rat_int.py``, and the
Dedekind-cut construction entirely on the path to ``R``: it goes from
``int`` to ``R`` directly. Rationals re-enter only as the image of
``Z * Z -> R`` given by ``(p, q) |-> [n |-> (p * n) DIV q]`` (or its
slope-respecting variant), and only when the user actually wants them.

------------------------------------------------------------------
The HOL encoding hurdle
------------------------------------------------------------------

HOL's only structural tool is ``new_basic_type_definition``
(``fusion.py:735``), which carves a subtype out of an existing type by
a non-empty predicate. So the construction lives entirely at the
function-space level:

  * ``slope : (int -> int) -> bool`` -- the almost-homomorphism
    predicate. No subtype yet -- a slope is just an ``int -> int``
    satisfying ``slope``.

  * ``slope_eq : (int -> int) -> (int -> int) -> bool`` -- the bounded
    -difference equivalence.

  * ``real`` -- carve out the subtype of ``int -> int`` whose elements
    are slopes. (The subtype is non-empty: the zero map is a slope.)

  * Reals proper are then ``real`` quotiented by ``slope_eq``. As in
    ``sets_as_trees.py``, we use a setoid presentation: keep working at
    ``real`` with ``slope_eq`` as the working equality, and only at the
    surface package the result with HOL ``=``.

(A genuine quotient type is also doable -- HOL4-style -- but the setoid
presentation keeps the kernel patch at zero.)

Boundedness on ``int`` is ``?N. !x. x in S ==> abs x <= N``. The
existential ``?N`` is HOL's standard SELECT-glue (see ``classical.py``);
no choice axiom beyond ``SELECT_AX`` is needed.
"""

# ---------------------------------------------------------------------------
# Stage 0 -- the integers.
# ---------------------------------------------------------------------------
#
# pyzar currently has integers only as the ``IS_INT_RAT`` *subset* of
# ``rat`` (``rat_int.py``, Definition 25). For Eudoxus we want a proper
# type ``int`` with its own ``+``, ``*``, ``<``, ``abs``. Two options:
#
# (a) Promote ``IS_INT_RAT`` to a subtype ``int`` of ``rat`` via
#     ``new_basic_type_definition``. Saves work because ring axioms
#     transfer for free; costs an extra ``rep``/``abs`` indirection on
#     every arithmetic operation, which never simplifies away cleanly.
#
# (b) Build ``int`` from ``num`` directly as the standard ``num x num``
#     quotient with (a, b) ~ (c, d) <=> a + d = c + b. Standalone,
#     reusable, and the ring axioms are first-order and short. ~200
#     lines plus ~50 lines of negation/abs lemmas. Independent of
#     ``frac.py`` and ``rat_int.py``, so the Eudoxus path can skip both
#     of those files entirely.
#
# We assume (b). The Eudoxus development imports ``int_add``,
# ``int_neg``, ``int_mul``, ``int_lt``, ``int_abs`` and the standard
# ring-with-order theorems on them.

# ---------------------------------------------------------------------------
# Stage 1 -- the slope predicate.
# ---------------------------------------------------------------------------
#
# defn:  defect f m n  :=  f (m + n) - f m - f n
#        slope f       :=  ?N. !m n. abs (defect f m n) <= N
#
# Proven facts at this layer (all elementary, no choice beyond SELECT
# for the ``?N`` glue):
#
#   |- slope (\n. 0)                                     (zero is a slope)
#   |- slope (\n. n)                                     (id is a slope; defect = 0)
#   |- slope (\n. q * n)                                 (any constant integer multiple)
#   |- slope f /\\ slope g ==> slope (\n. f n + g n)     (sum of slopes)
#   |- slope f ==> slope (\n. -(f n))                    (negation of a slope)
#   |- slope f /\\ slope g ==> slope (f o g)             (composition; the key lemma)
#
# The composition lemma is the heart of the algebra. The standard
# proof: if abs (defect f) <= M and abs (defect g) <= N, expand
# f (g (m+n)) - f (g m) - f (g n) by inserting and subtracting
# f (g m + g n); the first piece is bounded by M, the second by
# (Lipschitz-style) growth of f on the bounded set {defect g m n}, which
# in turn is bounded because f itself is "almost linear" on bounded
# sets. The full argument is ~30 lines of ``int`` inequalities; it is
# the longest single proof in the development.

# ---------------------------------------------------------------------------
# Stage 2 -- bounded-difference equivalence and the real type.
# ---------------------------------------------------------------------------
#
# defn:  bdiff f g  :=  ?N. !n. abs (f n - g n) <= N
#        slope_eq f g  :=  bdiff f g
#
# Standard lemmas:
#
#   |- slope f ==> slope_eq f f                          (reflexivity)
#   |- slope_eq f g ==> slope_eq g f                     (symmetry)
#   |- slope_eq f g /\\ slope_eq g h ==> slope_eq f h    (transitivity)
#
# Carve out ``real`` from ``int -> int`` by ``slope``:
#
#   |- slope (\n. 0)                                     (witness)
#   real  :=  new_basic_type_definition "real" "abs_real" "rep_real" ...
#
# Setoid wrapper: ``In_R x y := slope_eq (rep_real x) (rep_real y)``,
# operations defined on ``real`` and proven slope_eq-respecting. As in
# ``sets_as_trees.py``, we never need a proper quotient type -- we
# treat ``slope_eq`` as the working equality and prove that every
# definable construct respects it.
#
# (Exposing the *true* quotient as the user-facing type is doable too,
# via either (i) a second subtype carving out a canonical representative
# per equivalence class with SELECT, or (ii) a quotient-package patch.
# Either way, the inner setoid layer stays untouched.)

# ---------------------------------------------------------------------------
# Stage 3 -- field operations.
#
# Each constructor below takes ``real`` arguments, returns a ``real``,
# and is accompanied by the slope_eq-respect lemma plus the
# characterisation theorem matching the corresponding field axiom.
# ---------------------------------------------------------------------------

# ZERO  -- constant 0.
#   defn:  R0 := abs_real (\n. 0)
#   key:   |- !x. R_add R0 x = x   (mod slope_eq)

# ONE   -- identity.
#   defn:  R1 := abs_real (\n. n)
#   key:   |- !x. R_mul R1 x = x   (mod slope_eq)

# ADD   -- pointwise addition.
#   defn:  R_add x y := abs_real (\n. rep_real x n + rep_real y n)
#   resp:  |- slope_eq f1 f2 /\\ slope_eq g1 g2 ==>
#                 slope_eq (\n. f1 n + g1 n) (\n. f2 n + g2 n)
#   thm:   commutativity, associativity, R_add x R0 = x, additive inverse
#          (R_neg below). All routine: defects telescope, bounds add.

# NEG   -- pointwise negation.
#   defn:  R_neg x := abs_real (\n. -(rep_real x n))
#   thm:   |- !x. R_add x (R_neg x) = R0   (mod slope_eq)
#   proof: slope_eq (\n. f n + (-(f n))) (\n. 0) is immediate -- the
#          difference is identically zero.

# MUL   -- composition.
#   defn:  R_mul x y := abs_real (rep_real x o rep_real y)
#   resp:  |- slope_eq f1 f2 /\\ slope_eq g1 g2 ==>
#                 slope_eq (f1 o g1) (f2 o g2)
#   proof of resp: slope_eq f1 f2 gives bdiff (f1 - f2) bounded; slope
#          g1 plus slope_eq g1 g2 gives g1 - g2 bounded, and slopes are
#          "Lipschitz on bounded sets" (a corollary of the slope axiom),
#          so f2 o g1 ~ f2 o g2. Add f1 o g1 ~ f2 o g1 from bdiff
#          (f1 - f2) at the points g1 n. Two bounded pieces, sum
#          bounded.
#   thm:   associativity (= associativity of o), commutativity (the
#          *only* non-trivial field axiom -- slopes commute up to bdiff;
#          standard one-page proof using slope-additive-defect bounds),
#          distributivity, R_mul R1 x = x, multiplicative inverse for
#          x =/= 0 (R_inv below).

# INV   -- "almost inverse" of a non-zero slope.
#   defn:  R_inv x := abs_real (\n. SELECT m. abs (rep_real x m - n) <= bound)
#          (i.e. an integer m for which (rep_real x) m is approximately n;
#          such an m exists once x is non-zero, by the Archimedean
#          slope lemma).
#   thm:   |- !x. ~(slope_eq (rep_real x) (\n. 0)) ==>
#               slope_eq (rep_real x o R_inv x) (\n. n)
#   proof: existence of "approximate preimage" is the standard Eudoxus
#          division lemma (Arthan 2004, Lemma 9). Bounds chase through.

# ---------------------------------------------------------------------------
# Stage 4 -- order.
# ---------------------------------------------------------------------------
#
# defn:  R_pos x  :<=>  ?C N. !n. n >= N ==> rep_real x n >= C * n
#                       (i.e. f grows at least linearly with positive slope)
#        R_lt x y  :<=>  R_pos (R_sub y x)
#
# Standard lemmas:
#
#   |- !x. R_pos x \\/ slope_eq (rep_real x) (\n. 0) \\/ R_pos (R_neg x)   (trichotomy)
#   |- R_pos x /\\ R_pos y ==> R_pos (R_add x y)
#   |- R_pos x /\\ R_pos y ==> R_pos (R_mul x y)
#   |- R_pos R1
#   |- ~ R_pos R0
#
# Trichotomy is the only mildly delicate piece: a slope is either
# bounded above on N+ (then either equivalent to 0 or to a negative
# slope), or unbounded above (then positive). The case-split uses
# excluded middle (HOL has it via SELECT_AX) but no choice on
# infinite indexed sets.

# ---------------------------------------------------------------------------
# Stage 5 -- Archimedean property and completeness.
# ---------------------------------------------------------------------------
#
# Archimedean:
#   thm:   |- !x. ?n. R_lt x (R_of_int n)
#   proof: a slope f is bounded by C*|n| + D for some C, D (sub-linear
#          growth bound, immediate from the slope axiom by induction on
#          n); pick any integer > C * 1 + D + 1.
#
# Dedekind completeness:
#   thm:   |- !P. (?x. P x) /\\ (?u. !x. P x ==> R_le x u) ==>
#                 ?s. (!x. P x ==> R_le x s) /\\
#                     (!t. (!x. P x ==> R_le x t) ==> R_le s t)
#   proof: let M be the integer ceiling of an upper bound. Define
#          sup f n  :=  greatest k such that there exists x in P with
#                       rep_real x n >= k * 1.    (or, equivalently,
#                       SELECT-pick from the bounded non-empty set of
#                       such k).
#          Show ``sup f`` is a slope: defect bounded by 2 * (overall
#          slope-defect bound for the family, which is *not* uniform
#          but each individual ``rep_real x`` has its own bound that
#          enters only via x). Show it is the least upper bound.
#
#          The non-trivial step is the slope property of the "diagonal"
#          function. Arthan 2004 §5 has a clean five-line argument that
#          ports directly. No countable choice is used: the
#          characteristic SELECTs are over *bounded* integer sets and
#          collapse to ``min``/``max`` on a finite range.

# ---------------------------------------------------------------------------
# Stage 6 -- what *is* and *isn't* derived.
# ---------------------------------------------------------------------------
#
# Derived from the bare HOL kernel + ``int``:
#   * Field axioms (commutative ring, multiplicative inverses for
#     non-zero).
#   * Total order compatible with the field operations.
#   * Archimedean property.
#   * Dedekind completeness (every non-empty bounded-above set has a
#     supremum).
#
# Not needed:
#   * No new axioms. No TARSKI_A, no inaccessibility, no choice beyond
#     SELECT_AX (which HOL has anyway).
#   * No countable choice. Every existential in the development either
#     ranges over a *bounded* integer set (collapses to min/max) or is
#     witnessed constructively by a slope formula.
#   * No power set, no sets-of-rationals, no Cauchy sequence type.
#
# What this *doesn't* give:
#   * Second-order completeness ("every Dedekind-complete ordered
#     archimedean field is isomorphic to ours") is provable but
#     requires set-theoretic machinery to even *state* if we want it
#     about an arbitrary ordered field. As a property of *this* ``real``
#     type the relevant statements all go through.
#   * No claim about constructivity in the Bishop sense -- we use
#     classical case-splits via SELECT_AX. Removing those is possible
#     (Arthan's exposition is constructive) but is a separate exercise.

# ---------------------------------------------------------------------------
# Implementation roadmap
# ---------------------------------------------------------------------------
#
# The kernel needs no changes. All work is user-level libraries.
#
#   1. ``int.py`` (prerequisite, reusable beyond this file) -- subtype
#      of ``num x num`` modulo (a, b) ~ (c, d) <=> a + d = c + b. Ring
#      operations, order, ``abs``, ``int_of_num`` injection. Standard
#      Landau-style construction; ~250 lines including the Satz-by-Satz
#      ring/order proofs.
#
#   2. ``slope.py`` -- the ``slope`` predicate, ``defect``, slope_eq,
#      and the six closure lemmas (zero, id, sum, neg, scalar mul,
#      composition). Composition is the single heavy proof; the other
#      five are ~10 lines each. (~250 lines.)
#
#   3. ``eudoxus_reals.py`` (this file, fleshed out) -- carve out
#      ``real``, define R0, R1, R_add, R_neg, R_mul, R_inv, R_pos,
#      R_lt, prove field axioms, order axioms, Archimedean,
#      completeness. (~600 lines: ~30 lines of construction + ~50 lines
#      of proof per field/order lemma, plus completeness at ~100.)
#
#   4. (optional) ``rat_of_real.py`` -- inject ``rat`` into ``real``
#      via ``Q a b |-> [n |-> (a * n) div b]`` (slope-respecting), and
#      prove the image is the rationals as an ordered subfield. ~150
#      lines; only needed if downstream code wants explicit rationals
#      inside ``real`` rather than approached through the Archimedean
#      property.
#
# Total: ~1100 lines of new code (or ~950 without the rational
# embedding), zero new axioms, zero kernel patches.
#
# Comparison: the Dedekind-cut path needs a ``set_of_rat`` infrastructure
# (in pyzar terms, ``rat -> bool`` plus a closure-of-cuts subtype),
# four-way sign case splits for multiplication, and a completeness
# proof that takes set unions of cut families. Estimated ~1400-1600
# lines and far more bookkeeping. The Cauchy-sequence path needs a
# uniform-Cauchy multiplication argument and either countable choice
# or a SELECT-on-sequences gadget; ~1300 lines and a more subtle
# foundational story.
#
# Skippable shortcut: if ``int.py`` is deferred, the entire development
# can be redone with ``num -> num`` "almost-additive" maps (Schanuel's
# original N-flavoured presentation, with negatives reconstructed via
# a sign tag inside ``real``). Saves ``int.py`` but spreads ~80 lines
# of sign-bookkeeping across ``slope.py`` and the field-axiom proofs.
# Probably not worth it once ``int.py`` exists for any other reason.

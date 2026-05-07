"""Hereditarily finite sets via Ackermann's bit-encoding.

SKETCH ONLY -- this file lays out the construction; the proofs are
stubbed with strategy comments rather than executed. Scope is set by
the immediate downstream consumer ``godel_first.py``: we build only as
much HF as it needs (encoding for the syntax of Q + a model of Q).
The general ZF constructors (Pow, Repl, Sep) are noted but deferred to
a follow-up file -- ``godel_first.py`` does not call them.

Stage 1 (bit operations on ``nat0``) is now LIVE in ``bits.py``: see
the symbol list below. Everything else in this file is a sketch.

Axiomatic cost: zero. HOL + ``nat0`` + the bit-extensionality lemma
already proved in ``bits.py`` is the entire substrate.

------------------------------------------------------------------
The idea (Ackermann 1937)
------------------------------------------------------------------

A natural number ``n`` *is* a hereditarily finite set: write ``n`` in
binary, read off the positions of the 1-bits, and recursively decode
each position as another HF set. So

    0       = {}
    1       = {0}              = {{}}
    2       = {1}              = {{{}}}
    3       = {0, 1}           = {{}, {{}}}
    4       = {2}              = {{{{}}}}
    5       = {0, 2}           = {{}, {{{}}}}
    ...

The recipe collapses to a single arithmetical predicate:

    In x y   <=>   bit x of y is 1.

The encoding is a bijection between ``nat0`` and HF, and every HF
operation we need below becomes an arithmetic operation on ``nat0``.

------------------------------------------------------------------
Why no nominal type
------------------------------------------------------------------

The original sketch wrapped HF in a one-line subtype
(``new_basic_type_definition`` over ``\\n. T``) to keep ``+`` and
``*`` from accidentally typechecking on HF sets. For
``godel_first.py`` we never *want* to do nat0-arithmetic on a
"formula encoding" by accident -- but the formal cost of a subtype
is two coercions (``rep_hf``, ``abs_hf``) threaded through every
lemma. Drop the subtype: write ``hf_ty := nat0_ty`` as a plain alias.
If this turns out to bite us in ``godel_first.py``, reinstate the
subtype later -- it is a syntactic refactor, not a proof rewrite.
"""

# ---------------------------------------------------------------------------
# Stage 1 -- bit operations on nat0.   (DONE in bits.py)
# ---------------------------------------------------------------------------
#
# bits.py exports, all without new axioms:
#
#   Definitions
#     double, ODD, HALF, pow2, bit, set_bit
#     (DOUBLE_BASE/STEP, ODD_BASE/STEP, HALF_BASE/STEP,
#      POW2_BASE/STEP, BIT_BASE/STEP, BIT_STEP_AT,
#      SET_BIT_BASE/STEP, SET_BIT_BASE_AT/STEP_AT)
#
#   Lemmas
#     BIT_AT_ZERO            :  |- !i. bit i 0 = F
#     ODD_DOUBLE             :  |- !n. ODD (double n) = F
#     ODD_SUC0_DOUBLE        :  |- !n. ODD (SUC0 (double n)) = T
#     HALF_DOUBLE            :  |- !n. HALF (double n) = n
#     HALF_SUC0_DOUBLE       :  |- !n. HALF (SUC0 (double n)) = n
#     BIT_AT_POW2_SAME       :  |- !i. bit i (pow2 i) = T
#     BIT_AT_POW2_DIFF       :  |- !j i. ~(i = j) ==> bit i (pow2 j) = F
#     RECONSTRUCT            :  |- !n. n = COND (ODD n) (SUC0 (double (HALF n))) (double (HALF n))
#     HALF_LT_SUC0, HALF_LT_NZ
#     ZERO_BITS              :  |- !n. (!i. bit i n = F) ==> n = 0
#     BIT_EXTENSIONALITY     :  |- !n m. (!i. bit i n = bit i m) ==> n = m
#     BIT_AT_SET_BIT_SAME    :  |- !i n. bit i (set_bit i n) = T
#     BIT_AT_SET_BIT_DIFF    :  |- !i j n. ~(i = j) ==> bit j (set_bit i n) = bit j n
#     BIT_LT                 :  |- !n i. bit i n ==> nat0_lt i n      (bit-monotonicity)
#
# That covers everything Stage 2 / Stage 3 below need. Two operations
# we did NOT prove out in bits.py and will inline here when called for:
#
#   * clr_bit i n  -- companion to set_bit. Defined the same way
#                     (recursion on i, COND on ODD), with the same
#                     SAME / DIFF lemmas. Trivial port from set_bit;
#                     we add it only when the first caller appears.
#   * OR_below n f -- finite bitwise-OR of (f 0) ... (f n-1). Needed
#                     by ``Union`` and the godel_first.py tuple
#                     decoder; defined by recursion on n with set_bit.

# ---------------------------------------------------------------------------
# Stage 2 -- HF and In.
# ---------------------------------------------------------------------------
#
#   hf_ty   := nat0_ty                            (alias; no subtype)
#   In x y :<=> bit x y                           (HOL bool)
#
# That's it. ``In`` is just ``bit`` under a friendlier name.
#
# Membership lemmas reduce to the bit lemmas already in bits.py:
#
#   |- ~In x Empty                                from BIT_AT_ZERO
#   |- !x y. In x y ==> nat0_lt x y               from BIT_LT  (foundation core)
#   |- !a b. (!x. In x a = In x b) ==> a = b      from BIT_EXTENSIONALITY
#                                                 (extensionality, immediate)
#
# No proof needed beyond a definitional unfolding step. ~30 lines.

# ---------------------------------------------------------------------------
# Stage 3 -- HF constructors needed by godel_first.py.
#
# What godel_first.py uses from this stage:
#   (a) Empty, Insert, Singleton, Pair        -- to encode Q syntax as
#                                                 finite tuples (HF trees).
#   (b) Pair_ord (ordered Kuratowski pair)    -- to encode (index, value)
#                                                 entries inside a tuple.
#   (c) Union                                 -- to define the von Neumann
#                                                 successor in the model
#                                                 of Q (Stage 6 below).
#   (d) Foundation as a derived rule          -- to argue that the
#                                                 minimum-bit element
#                                                 of any nonempty HF set
#                                                 has no member also in it.
#                                                 Drops out of BIT_LT.
#
# What godel_first.py does NOT use, and is therefore deferred:
#   * Pow, Repl, Sep  -- the general ZF constructors. Doable in HF
#     (sketches in the original draft of this file); they are not
#     called from anywhere in the godel_first chain. Punt to a future
#     ``hf_zf.py`` if/when a consumer wants full ZF surface.
#   * Refutation of Infinity. A nice theorem, also deferred -- the
#     consistency-of-Q argument in godel_first.py uses the *positive*
#     fact that HF models Q, not the negative fact that HF refutes
#     Infinity.
# ---------------------------------------------------------------------------

# EMPTY  -- numeric 0.
#   defn:  Empty := 0
#   thm:   |- !x. ~In x Empty
#   proof: BIT_AT_ZERO.

# INSERT i s -- add element i.
#   defn:  Insert i s := set_bit i s
#   thms:  |- !i s. In i (Insert i s) = T                  (BIT_AT_SET_BIT_SAME)
#          |- !i j s. ~(i = j) ==> In j (Insert i s) = In j s
#                                                          (BIT_AT_SET_BIT_DIFF)
#   note:  no proof work -- both lemmas are direct renames.

# SINGLETON x -- {x}.
#   defn:  Singleton x := Insert x Empty   = pow2 x
#   thm:   |- !x y. In y (Singleton x) = (y = x)
#   proof: BIT_AT_POW2_SAME / BIT_AT_POW2_DIFF + EXCLUDED_MIDDLE.
#          ~10 lines.

# PAIR x y -- {x, y}  (unordered).
#   defn:  Pair x y := Insert x (Singleton y)
#   thm:   |- !a b z. In z (Pair a b) = (z = a \\/ z = b)   (PAIRING)
#   proof: case-split on z=a; INSERT lemmas + SINGLETON. ~15 lines.

# PAIR_ORD x y -- Kuratowski (x, y) := {{x}, {x, y}}.
#   defn:  Pair_ord x y := Pair (Singleton x) (Pair x y)
#   thm:   |- !a b c d. Pair_ord a b = Pair_ord c d
#                       <=> (a = c /\\ b = d)              (ordered-pair char.)
#   proof: forward direction by EXTENSIONALITY: equal sets share their
#          singleton coordinate, hence a = c; the {a,b} = {c,d} clause
#          then pins b = d once a = c. Reverse direction immediate.
#          ~30 lines, the only mildly substantive lemma in Stage 3.

# UNION y -- bitwise OR of bits of members of y.
#   defn:  Union y := OR_below (SUC0 y)
#                              (\i. COND (bit i y) (rep_member i) 0)
#          where rep_member i = i  (the HF member at bit position i).
#          Concretely: bit x (Union y) = T  iff
#                      ?i. bit i y /\\ bit x i.
#          Implementation: recursion on a numeric "scan bound";
#          BIT_LT gives ``~(bit i y) for i >= y``, so ``SUC0 y`` is a
#          safe upper bound.
#   thm:   |- !y x. In x (Union y) = ?z. In x z /\\ In z y     (UNION)
#   proof: bit-extensionality + the OR_below characterisation lemma.
#          ~50 lines including the OR_below scaffolding.

# FOUNDATION (as a derived rule, not a constructor).
#   thm:   |- !a. (?x. In x a) ==>
#                 ?x. In x a /\\ ~(?y. In y a /\\ In y x)
#   proof: ``In`` strictly decreases the numeric value (BIT_LT).
#          So given any non-empty ``a``, the numerically-smallest
#          element x of ``In . a`` (well-ordering of nat0) has
#          no member also in ``a`` -- any such y would be smaller
#          still, contradicting minimality.
#          ~25 lines once nat0 well-ordering is invoked.
#   note:  this is the slickest payoff of the encoding -- foundation
#          becomes the well-ordering of the natural numbers.

# ---------------------------------------------------------------------------
# Stage 4 -- a model of Q inside HF.   (used by godel_first.py Stage 6)
# ---------------------------------------------------------------------------
#
# This is the *only* substantive client of Stage 3 from
# godel_first.py: the model construction that discharges the
# consistency assumption.
#
# Define the von Neumann numerals as a HOL function vN : nat0 -> hf:
#
#   vN 0       := Empty                                          ( = 0 )
#   vN (S n)   := vN_succ (vN n)
#                where vN_succ x := Union (Pair x (Singleton x))
#                                = Insert x x
#                                  -- equivalent in HF; the latter is
#                                  -- one bit-flip and avoids the
#                                  -- ordered-pair detour. Both forms
#                                  -- agree because Singleton x = {x}
#                                  -- and Union {x, {x}} = x ∪ {x}.
#
# We pick the ``Insert x x`` form to keep proofs short:
#
#   thm:   |- !n. vN_succ (vN n) = set_bit (vN n) (vN n)
#                                                    (definition unfold)
#
# The four lemmas godel_first.py Stage 6 actually consumes, with
# their proof sketches:
#
#   VN_SUCC_NEQ_ZERO  :  |- !n. ~(vN_succ (vN n) = Empty)
#     Proof: vN_succ x = set_bit x x, which has bit x set
#            (BIT_AT_SET_BIT_SAME), but bit x 0 = F (BIT_AT_ZERO).
#            So vN_succ x != 0 = Empty.    ~10 lines.
#
#   VN_SUCC_INJ        :  |- !m n. vN_succ m = vN_succ n ==> m = n
#     Proof: from set_bit m m = set_bit n n, take HALF on both sides:
#            vN_succ x peels exactly one bit at position x, so HALF
#            recovers x in each case... actually cleaner: bit x of
#            set_bit m m is "T iff x = m \\/ bit x m". The maximum
#            bit position of set_bit m m is therefore max(m, max-bit(m))
#            = m (because BIT_LT gives every set bit of m below m,
#            but bit m itself is set). So m = n via the maximum-bit
#            characterisation. ~40 lines, the bulk being the
#            "maximum bit position" lemma. (Alternative shortcut:
#            argue via cardinality / bit-extensionality directly;
#            comparable length.)
#
#   VN_PRED            :  |- !x. ~(x = Empty) ==> ?y. x = vN_succ y
#     Stated WITHIN the image of vN: i.e. only required when x is
#     itself a vN numeral. This is what Q3 needs in the model.
#     Proof: case-split on x = vN 0 (impossible by hypothesis) vs
#            x = vN (S k); the latter directly gives y := vN k.
#            ~15 lines plus a vN-image case-analysis lemma
#            (provable by cases_on EXCLUDED_MIDDLE on x = vN 0,
#            then nat0 induction extracting the predecessor).
#
#   VN_INJ             :  |- !m n. vN m = vN n ==> m = n
#     The embedding is injective. Used to bridge HOL equality on
#     numerals and Q-internal equality. Proof: nat0 induction on
#     m with case-split on n; VN_SUCC_NEQ_ZERO + VN_SUCC_INJ.
#     ~25 lines.
#
# Arithmetic on vN-numerals (Q4-Q7):
#
#   defn:  vN_plus  x y := vN ((rep x) + (rep y))      via VN_INJ
#          vN_times x y := vN ((rep x) * (rep y))
#     where ``rep`` is the (HOL-level, total but only canonical on
#     the vN image) inverse of vN. We do NOT need ``rep`` to be
#     definable in the object language Q -- it is a HOL convenience
#     used to *define* vN_plus / vN_times as functions on hf, then
#     the Q-axiom proofs reduce to nat0-arithmetic identities.
#
#   thm:   VN_PLUS_ZERO   : |- !x. vN_plus x (vN 0)     = x
#          VN_PLUS_SUCC   : |- !x y. vN_plus x (vN_succ y) = vN_succ (vN_plus x y)
#          VN_TIMES_ZERO  : |- !x. vN_times x (vN 0)    = vN 0
#          VN_TIMES_SUCC  : |- !x y. vN_times x (vN_succ y) = vN_plus (vN_times x y) x
#     Each is one nat0-arithmetic line plus VN_INJ to translate.
#     ~10 lines apiece, ~50 total.
#
# Bundle: Q1 -> VN_SUCC_NEQ_ZERO; Q2 -> VN_SUCC_INJ; Q3 -> VN_PRED;
#         Q4-Q7 -> VN_PLUS_*, VN_TIMES_*. Together they give the
#         "HF |= Q" theorem godel_first.py Stage 6 imports.
#
# Total Stage 4: ~150 lines (definitions + 4 + 4 named lemmas).

# ---------------------------------------------------------------------------
# Stage 5 -- bi-interpretation, briefly.
# ---------------------------------------------------------------------------
#
# Ackermann's theorem (1937): PA and ZF - Infinity prove the same
# arithmetic sentences. The forward translation is the encoding above
# (every set is a natural number); the reverse is "the natural
# numbers are the von Neumann ordinals" -- which is what Stage 4
# explicitly constructs.
#
# In pyzar this means: any theorem of HF (Stages 1-4 here) is an
# arithmetic theorem of nat0, and conversely any arithmetic theorem
# transports to an HF statement via vN. We do NOT mechanise the
# bi-interpretation as an internal proof translation -- we only need
# its semantic upshot (Stage 4 above). godel_first.py uses neither
# direction explicitly; the bi-interpretation is conceptual scaffolding.

# ---------------------------------------------------------------------------
# Implementation roadmap (revised against godel_first.py)
# ---------------------------------------------------------------------------
#
# Prerequisites: bits.py (DONE), nat0_order.py (DONE), parts of nat.py
# (+, *, < on nat0; the additive/multiplicative parts already exist
# from the rationals-construction work).
#
#   1. Stage 2: hf alias + In definition. ~10 lines, no proof work.
#
#   2. Stage 3: Empty, Insert, Singleton, Pair, Pair_ord, Union,
#      plus the Foundation derived rule. ~150 lines.
#      Pair_ord and Union are the only new substance; the rest are
#      one-step renames of bits.py lemmas.
#
#   3. Stage 4: vN, vN_succ, vN_plus, vN_times, plus the eight
#      Q-axiom lemmas. ~150 lines.
#
#   Total here: ~310 lines. (Down from ~350 in the original sketch
#   thanks to dropping Pow / Repl / Sep / refutation-of-Infinity.)
#
# Comparison: the original sketch was ~500 lines aimed at full ZF
# surface. The trim above sheds roughly 40% of that scope. If a
# downstream consumer turns up wanting Pow / Repl / Sep, restore them
# in a sibling ``hf_zf.py`` rather than enlarging this file -- the
# Q-model construction stays cleanest when not entangled with the
# generic constructors.
#
# Optional follow-ups (each strictly downstream of this file):
#   * ``hf_zf.py``     -- Pow, Repl, Sep, refutation of Infinity.
#                         Needed only if someone wants Landau Saetze
#                         1-150 over the formalised ZF surface.
#                         ~250 lines.
#   * ``hf_arith.py``  -- ``rep`` on the vN image as an actual nat0
#                         function (HOL-level, not Q-internal),
#                         giving the PA <-> ZF-Inf transport
#                         concretely. ~150 lines. Strictly nice-to-
#                         have; godel_first.py does not call it.

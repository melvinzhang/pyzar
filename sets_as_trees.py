"""Aczel's sets-as-trees model of ZF over the bare HOL kernel.

SKETCH ONLY -- this file lays out the construction; the proofs are
stubbed with strategy comments rather than executed. The goal is to
replace the seven ZF axioms posted in ``tg_set_theory.py``
(EXTENSIONALITY, FOUNDATION, PAIRING, UNION, POWERSET, REPLACEMENT,
INFINITY) with *theorems* derived from HOL's existing axioms
(ETA_AX, SELECT_AX, INFINITY_AX). TARSKI_A cannot be derived -- it
asserts an inaccessible cardinal, which is strictly stronger than ZFC,
so it remains a single posted axiom. Net: 7 axioms -> 1 axiom.

------------------------------------------------------------------
The idea (Aczel 1978; Werner, "Sets in Types, Types in Sets" 1997)
------------------------------------------------------------------

A set is a well-founded tree whose nodes have arbitrary branching.
Formally, the inductive type

    V  ::=  sup (A : Type) (f : A -> V)

with extensional equality

    sup A f  ~  sup B g
       <=>  (!a. ?b. f a ~ g b) /\\ (!b. ?a. f a ~ g b)

and membership

    x in (sup A f)  <=>  ?a. x ~ f a.

Every ZF axiom becomes a constructive *operation* on trees:

    Pairing(x, y)   = sup bool    (\\b. if b then x else y)
    Union(x)        = sup (Sigma a. dom (f a))    (uncurry of f)
    Powerset(x)     = sup (A -> bool) (\\p. sup {a | p a} f)
    Replacement(R)  = sup (dom of x) (R-image)
    Infinity        = sup nat (iterate succ Empty)
    Foundation      = induction on the tree (no infinite descent)

Extensionality is exactly the definition of ``~``. None of these need
choice; they are first-order constructions in the host metatheory.

------------------------------------------------------------------
The HOL encoding hurdle
------------------------------------------------------------------

HOL has no native inductive types and no type universe -- ``V`` cannot
literally be ``sup A (A -> V)`` for arbitrary ``A``. Two standard
workarounds:

(a) Fix one large branching type. Choose a single ``ind``-indexed
    branching: ``V := ind -> V option``. Since ``ind`` is infinite,
    every countable-or-smaller set fits. ZF holds *relative to ``ind``*:
    Pairing/Union/Powerset stay inside whatever cardinality ``ind``
    realises, and Replacement holds because R-images are no larger
    than their domain. POWERSET past ``ind`` is the catch -- we need
    ``ind`` strictly larger than every level we want to populate.

(b) Use a Scott-style D_infinity construction: take ``V`` as a domain
    equation solved as a fixpoint over ``ind``-indexed approximants.
    More machinery, no qualitative gain over (a) for our purposes.

We take (a). The honest statement of what we get is:

    Theorem (Werner). HOL + (``ind`` is strongly inaccessible) proves
    the ZF axioms over a defined type ``V`` with defined ``In``.

The inaccessibility-of-``ind`` assumption is exactly TARSKI_A in disguise.
So the axiomatic budget shifts from "7 ZF axioms" to "1 inaccessibility
axiom about the existing HOL type ``ind``" -- the same single axiom
``tg_set_theory.py`` already posts, just relocated to be about ``ind``
instead of about a fresh type ``V``.

(Without inaccessibility, we still get *bounded* ZF -- everything except
unrestricted Powerset -- which is enough for arithmetic, the rationals,
the reals, and Landau-style analysis. That is itself a useful target.)
"""

# ---------------------------------------------------------------------------
# Stage 1 -- raw trees: T := ind -> T option, encoded as a subtype.
# ---------------------------------------------------------------------------
#
# HOL has no recursive types, so ``T`` is *carved out* of the HOL function
# space ``ind -> ind`` (or any sufficiently rich function space) via a
# well-foundedness predicate. The standard recipe:
#
#   1. Define ``Path`` -- finite sequences of branch indices. pyzar has
#      no ``list`` type, so we encode paths as ``nat -> ind`` paired with
#      a length, or via Cantor pairing into a single ``nat``. (Adding a
#      proper ``list.py`` is the cleaner option and is reusable.)
#   2. A "raw tree" is a predicate ``r : Path -> bool`` marking which
#      paths are present, with the prefix-closed and well-founded
#      restrictions. The empty path is always present (root); a leaf has
#      no extensions; ``r`` admits no infinite descending chain.
#   3. Define ``T_PRED : (Path -> bool) -> bool`` capturing those
#      restrictions, prove ``|- ?r. T_PRED r`` (the ``always-False except
#      at the empty path'' tree witnesses), and use the kernel primitive
#      ``new_basic_type_definition`` (``fusion.py:735``) to introduce
#      ``T`` as a subtype with an ``abs`` / ``rep`` isomorphism pair.
#
# Kernel support: nothing extra needed. ``new_basic_type_definition`` is
# already exposed and is exactly the standard HOL primitive for this.
# What is missing is purely user-level scaffolding (see roadmap below).
#
# Children-of: ``children : T -> ind -> T option``. Read off the tree
# via path extension. ``None`` at index ``i`` means "no i-th child".

# ---------------------------------------------------------------------------
# Stage 2 -- bisimulation equality and membership.
# ---------------------------------------------------------------------------
#
# Tree equality on raw trees is *not* HOL equality: two trees with the
# same children up to permutation must be identified. We define
#
#   Tree_eq t1 t2  <=>
#       (!i. children t1 i = Some c1 ==>
#            ?j c2. children t2 j = Some c2 /\\ Tree_eq c1 c2)
#       /\\ (symmetric clause)
#
# as the greatest fixpoint of the corresponding monotone operator on
# ``T -> T -> bool`` (Knaster-Tarski via SELECT_AX, the standard HOL
# move; see ``classical.py`` for the SELECT-based existential glue). On
# *well-founded* trees the gfp coincides with the lfp, so induction on
# tree height works for proofs.
#
# Then ``V`` is the quotient of ``T`` by ``Tree_eq``. In HOL we don't
# need actual quotient types -- we keep working at the ``T`` level and
# treat ``Tree_eq`` as the working equality, defining
#
#   In x y  <=>  ?i c. children y i = Some c /\\ Tree_eq x c
#
# and lifting all subsequent constructs to be ``Tree_eq``-respecting.
# A thin "setoid" wrapper at the surface gives the user an honest type
# ``V`` with HOL equality matching ``Tree_eq``.
#
# (Quotient types proper are also doable -- HOL4 has them -- but the
# setoid presentation keeps the kernel patch small.)

# ---------------------------------------------------------------------------
# Stage 3 -- ZF axioms as theorems.
#
# Each constructor below takes ``T``-level arguments and returns a ``T``,
# accompanied by a characterisation theorem stating its membership
# behaviour. The characterisation theorem is exactly the corresponding
# ZF axiom.
# ---------------------------------------------------------------------------

# EMPTY  -- the tree with no children.
#   defn:  Empty := the unique tree with children _ = None
#   thm:   |- !x. ~In x Empty                     (matches EMPTY_PROP)

# PAIR x y  -- branching by ``bool``.
#   defn:  pair x y := tree with children 0 = Some x, children 1 = Some y,
#                      children _ = None
#   thm:   |- !a b. ?p. !x. In x p = (x = a \\/ x = b)     (PAIRING)
#   proof: take p := pair a b; unfold In and children; case-split on i.

# UNION x  -- flatten one level.
#   defn:  union x := tree whose paths are concatenations
#                     "i :: js" with i a child-index of x and js a
#                     child-path of (children x i).
#   thm:   |- !a. ?u. !x. In x u = (?y. In x y /\\ In y a)   (UNION)
#   proof: directly from path concatenation; existential over ``i``
#          becomes existential over ``y``.

# POW x  -- branching by ``ind -> bool`` (subset characteristic).
#   defn:  pow x := tree indexed by p : ind -> bool, child at p =
#                   the subtree of x restricted to indices i with p i.
#   thm:   |- !a. ?p. !x. In x p = Subset x a              (POWERSET)
#   proof: characteristic-function correspondence; uses Tree_eq on the
#          subset side and SELECT to reconstruct the witness ``p``.
#   caveat: requires ``ind -> bool`` injects into ``ind`` for the result
#           to live in ``T``. This is the inaccessibility hypothesis.

# REPL R x  -- image under a HOL relation.
#   defn:  repl R x := tree indexed by the same indices as x, child at i
#                     = the unique y with R (children x i) y, when R is
#                     functional on x.
#   thm:   |- !a. (functionality on a) ==>
#               ?b. !y. In y b = ?x. In x a /\\ R x y       (REPLACEMENT)
#   proof: existential lifted via SELECT; Tree_eq compatibility shows R
#          respects bisimulation when functional.

# OMEGA  -- iterated successor from INFINITY_AX.
#   defn:  omega := tree indexed by ind, child at the n-th iterate of
#                   the ONE_ONE not-ONTO function = succ^n(Empty),
#                   where succ x := union (pair x (pair x x)).
#   thm:   |- ?I. (?z. In z I /\\ ~(?w. In w z)) /\\
#                 (!x. In x I ==> ?y. In y I /\\
#                                     !w. In w y = (In w x \\/ w = x))
#                                                            (INFINITY)
#   proof: the ind -> ind injection from INFINITY_AX gives an
#          ind-indexed family; transport through Tree_eq.

# EXTENSIONALITY -- by definition of Tree_eq.
#   thm:   |- !a b. (!x. In x a = In x b) ==> a = b
#   proof: unfold In on both sides; the hypothesis is exactly the
#          unfolded Tree_eq; conclude via the setoid wrapping.

# FOUNDATION -- by tree-height induction.
#   thm:   |- !a. (?x. In x a) ==>
#                 ?x. In x a /\\ ~(?y. In y a /\\ In y x)
#   proof: well-foundedness of T (built into the subtype predicate)
#          gives a minimal-rank element among ``In . a``; that element
#          has no member also in ``a`` since any such member would have
#          strictly smaller rank, contradicting minimality.

# ---------------------------------------------------------------------------
# Stage 4 -- what *cannot* be derived: TARSKI_A.
# ---------------------------------------------------------------------------
#
# TARSKI_A says every set sits inside a Grothendieck universe. In the
# tree model this is "every tree is a member of an inaccessible-rank
# subtree". The construction needs an inaccessible cardinal kappa with
# kappa <= |ind|; ZFC alone does not prove inaccessibles exist, and
# neither does HOL with ``ind`` infinite.
#
# Two clean options:
#
# (i)  Keep TARSKI_A as a posted axiom about V, identical to the form
#      in ``tg_set_theory.py``. Net: 1 axiom, replaces 7.
#
# (ii) Post inaccessibility of ``ind`` directly as a HOL axiom. This is
#      arguably cleaner since it is a statement about the existing
#      kernel type rather than about the derived ``V``. The closure
#      clauses of TARSKI_A then drop out, because POW_PROP already
#      lives inside ``ind``.
#
# Either way, INACCESSIBLE_UNIVERSE in ``tg_set_theory.py`` becomes a
# straight repackaging just as it is now.

# ---------------------------------------------------------------------------
# Implementation roadmap
# ---------------------------------------------------------------------------
#
# The kernel needs no changes -- ``new_basic_type_definition`` is already
# present (``fusion.py:735``). All work is user-level libraries.
#
#   1. ``list.py`` (optional but recommended) -- finite lists over a
#      type variable, defined as a subtype of ``nat -> A`` paired with a
#      length. Reusable beyond this file. (~100 lines.) Skippable if we
#      Cantor-pair paths into ``nat`` instead, at the cost of clarity.
#
#   2. ``trees.py`` -- subtype ``T`` of path predicates carved out by
#      well-foundedness; ``children : T -> ind -> T option``; Tree_eq as
#      a greatest fixpoint via the closed form
#         ``Tree_eq x y := !P. (P bisimulation) ==> P x y``
#      (no Knaster-Tarski machinery needed -- the gfp is definable
#      directly because HOL has higher-order quantification).
#      (~150 lines.)
#
#   3. ``v.py`` -- setoid wrapper; In; Empty / Pair / Union / Pow /
#      Repl / Omega constructors with their characterisation theorems.
#      Each constructor is ~30 lines of construction + ~30 lines of
#      proof that the characterisation holds. (~400 lines.)
#
#   4. Replace the seven ``new_axiom`` calls in ``tg_set_theory.py``
#      with imports from ``v.py``. TARSKI_A and everything below it
#      compiles unchanged.
#
# Total: ~550-650 lines of new code, deleting 7 axioms, no kernel patch.
# The bisimulation infrastructure is reusable for any future
# coinductive constructions (streams, processes, ...).
#
# Skippable shortcut: if ``list.py`` feels like scope creep, the entire
# project can be done with ``nat`` paths and Cantor pairing, at maybe
# +50 lines of bookkeeping inside ``trees.py``. The honest tradeoff is
# readability of the path-manipulation lemmas.

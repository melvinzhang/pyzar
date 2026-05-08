# ---------------------------------------------------------------------------
# Stage 3 -- representability of primitive recursive functions in Q.
# ---------------------------------------------------------------------------
#
# A function f : num -> num is *represented* in Q by a formula
# F_f(x, y) iff
#
#     |- !n. Prov_Q (F_f(numeral n, numeral (f n)))
#     |- !n. Prov_Q (!y. F_f(numeral n, y) -> y = numeral (f n)).
#
# Theorem (representability). Every primitive recursive function is
# representable in Q.
#
# This is the headline weak-arithmetic result and the *whole reason* Q
# suffices for incompleteness despite lacking induction. The standard
# proof (Boolos-Burgess-Jeffrey, "Computability and Logic" Ch. 16-17):
#
#   * Constants, projections, successor, addition, multiplication: by
#     direct unfolding against axioms Q4-Q7.
#   * Composition: substitution; routine.
#   * Primitive recursion: this is where induction would normally
#     enter. Q lacks it, so we use Goedel's beta function -- a fixed
#     ternary arithmetic predicate beta(a, b, i, y) such that, for any
#     finite sequence (y_0, ..., y_k), there exist a, b with
#     beta(a, b, i, y_i) for each i <= k. The standard construction
#     is via Chinese remainder; the existence proof for any given
#     finite sequence is a numeric calculation that Q proves for each
#     numeral instance. Recursion equations then encode as the
#     existence of an a, b coding the trajectory.
#
# In our HOL setting we don't need the full primitive recursion result
# -- we only need representability of three specific predicates:
#
#   (i)   ``Proof_Q``     (decidable, hence representable; the
#                          formula is an explicit bounded-quantifier
#                          encoding of the proof-checking procedure).
#   (ii)  ``substitute``  (primitive recursive on godelnums).
#   (iii) ``godelnum``    (degenerate -- it is just a HOL function on
#                          encoded syntax; we represent its numeral
#                          image rather than the function itself).
#
# Each of these is a several-page proof in textbook treatments. The
# slick HOL move is to define the representing formulas *by* the HOL
# definitions, transported through the bounded-quantifier translation,
# and then show by induction (in the *meta*theory; HOL has it) on
# syntactic complexity that Q proves the right characterisations.
# ~500 lines, with the beta-function lemma factored out.
#
# (No saving here over PA: representability is exactly as hard with
# induction as without it; the beta-function trick was invented
# precisely so that the proof would not depend on induction. The
# saving over PA is at Stage 2.)
#
# Output:
#
#   defn:  Prov_Q_internal : term -> form
#          (the Q formula expressing "the term coded by x is provable")
#   thm:   |- !n. Prov_Q n <==>
#                Prov_Q (godelnum (Prov_Q_internal (numeral n)))
#                                                    (representability)

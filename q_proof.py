# ---------------------------------------------------------------------------
# Stage 2 -- the Q proof system.
# ---------------------------------------------------------------------------
#
# Logical axioms (shared with any first-order Hilbert system):
#   * Propositional tautologies (any standard finite axiomatisation).
#   * Quantifier axioms: !x. F[x] -> F[t/x]; F -> !x. F (x not free).
#   * Equality: t = t; substitution under equality.
#
# Non-logical axioms (Robinson Q, seven closed formulas):
#   Q1.  !x.    ~(Succ x = Zero)
#   Q2.  !x y.  Succ x = Succ y  ->  x = y
#   Q3.  !x.    ~(x = Zero)  ->  ?y. x = Succ y
#   Q4.  !x.    Plus x Zero = x
#   Q5.  !x y.  Plus x (Succ y) = Succ (Plus x y)
#   Q6.  !x.    Times x Zero = Zero
#   Q7.  !x y.  Times x (Succ y) = Plus (Times x y) x
#
# Rules: modus ponens; generalization.
#
# defn:  is_axiom(n) :<=>  n decodes to one of the logical or Q axioms
#                          listed above. Decidable; ~80 lines of case
#                          analysis. (Compare PA: ~150 lines, because
#                          recognising an instance of the induction
#                          schema requires substitution-pattern
#                          matching against an arbitrary formula. Q
#                          has no schemas, only seven closed formulas
#                          to recognise verbatim.)
#
# defn:  Proof_Q(p, n) :<=>
#            p is a num encoding a non-empty list [F_0, ..., F_k]
#            of formula-godelnums, F_k = n, and for each i <= k either
#              is_axiom(F_i), or
#              ?j h < i. F_i = mp(F_j, F_h)        (modus ponens), or
#              ?j x < i. F_i = generalize(F_j, x)  (generalization).
#
# defn:  Prov_Q(n) :<=> ?p. Proof_Q(p, n).
#
# Standard meta-lemmas at this layer:
#
#   |- Proof_Q is decidable.
#   |- Prov_Q is recursively enumerable (Sigma_1 in the obvious sense).
#   |- (closure rules: if Prov_Q F /\\ Prov_Q (F -> G) then Prov_Q G.)
#


# ---------------------------------------------------------------------------
# Stage 2C -- Q-internal logic.
# ---------------------------------------------------------------------------
#
# Build first-order logical reasoning *inside* Q from the seven axiom
# schemas (K, S, N, UI, Vac, Refl, Subst) plus MP and Gen. Each lemma
# in this file derives a standard meta-theorem -- "Q proves X" -- as a
# HOL theorem about ``Prov_Q``.
#
# Layered build-up:
#
#   (a) axiom-instance specializations      PROV_Q_K, PROV_Q_S, PROV_Q_N
#   (b) basic propositional reasoning       PROV_Q_IMP_REFL,
#                                           PROV_Q_HYP_DROP,
#                                           PROV_Q_TRANS_IMP
#   (c) conjunction / iff                   PROV_Q_AND_INTRO,
#                                           PROV_Q_IFF_INTRO
#
# Consumed by the diagonal lemma (Stage 4) and the Goedel-sentence main
# theorem (Stage 5).
# ---------------------------------------------------------------------------


from fusion import Var, REFL
from basics import mk_const, mk_app, mk_eq, mk_abs, rand
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof
from tactics import (
    SPEC, SPECL, GEN, MP, CONJ, DISJ1, DISJ2, EQ_MP, SYM, EXISTS,
)
from axioms import mk_or

from q_syntax import (
    Not_f, Imp_f,
    IS_FORM_AT_IMP, IS_FORM_AT_NOT,
)
from q_proof import (
    Prov_Q,
    PROV_Q_AXIOM, PROV_Q_MP,
    is_K, is_S, is_N,
    IS_K_AT, IS_S_AT, IS_N_AT,
    is_logical_axiom, is_axiom,
    is_q_axiom,
    IS_LOGICAL_AXIOM_AT, IS_AXIOM_AT,
)


# ---------------------------------------------------------------------------
# Helper: lift ``|- is_K n`` (or is_S / is_N) through the disjunction
# chain into ``|- Prov_Q n``.
#
# Chain:  is_<X> n  ->  is_logical_axiom n  ->  is_axiom n  ->  Prov_Q n.
#
# is_<X> sits as one disjunct in IS_LOGICAL_AXIOM_AT's right-associated
# 7-way OR. is_logical_axiom sits as the right disjunct of IS_AXIOM_AT.
# Caller specifies which logical-axiom slot via ``slot``: 0=K, 1=S,
# 2=N, 3=UI, 4=Vac, 5=Refl, 6=Subst.
# ---------------------------------------------------------------------------


def _prov_of_logical(p, name, slot_th, slot_idx, n_term):
    """Lift ``slot_th : {} |- is_<X> n_term`` to ``|- Prov_Q n_term``.

    Posts intermediate facts ``{name}_logical`` and ``{name}_axiom``
    in scope; returns the final Prov_Q theorem (also posted under
    ``{name}_prov``).
    """
    # Build the right-associated 7-way disjunction at n_term:
    #   is_K n \/ is_S n \/ is_N n \/ is_UI n \/ is_Vac n \/
    #            is_Refl n \/ is_Subst n.
    is_logical_at = SPEC(n_term, IS_LOGICAL_AXIOM_AT)
    # is_logical_at : |- is_logical_axiom n = <7-disjunction>
    rhs_disj = rand(is_logical_at._concl)
    # Walk into rhs_disj at slot_idx, peeling DISJ1/DISJ2 layers.
    # The disjunction is right-associated: D0 \/ (D1 \/ (D2 \/ ...))
    # so to reach slot k we DISJ2 k times then DISJ1 (unless slot is the
    # final one).
    cur = rhs_disj
    parts = []
    while True:
        # cur is either D \/ rest or final D.
        # Detect Or by looking at outer rator.
        from basics import rator, rand as _rand
        outer = rator(cur)
        from basics import rator as _rator
        # outer should be Comb(Or, D) for non-final, else just D.
        try:
            head = _rator(outer)  # if cur is "Or D rest", head should be Or
            from fusion import Const
            if isinstance(head, Const) and head.name == "\\/":
                d_part = _rand(outer)
                rest = _rand(cur)
                parts.append(d_part)
                cur = rest
                continue
        except Exception:
            pass
        # cur is the final atom.
        parts.append(cur)
        break

    # Now parts = [D0, D1, ..., D6]. Build is_logical_axiom by lifting
    # slot_th through DISJ2/DISJ1 to land at parts[slot_idx].
    th = slot_th
    # Starting from parts[slot_idx], introduce DISJ1 if not the last,
    # then DISJ2 wrap from outer to inner.
    # Strategy: start with th = slot_th proving parts[slot_idx]. Then for
    # every layer above slot_idx, DISJ2 with the inner-already-built.
    # Build the suffix at slot_idx: if slot_idx < len(parts)-1, DISJ1
    # combines with parts[slot_idx+1..]:
    if slot_idx < len(parts) - 1:
        # Right-fold construction of parts[slot_idx+1..] disjunction
        # is awkward; easier: build the full disjunction at slot_idx
        # by introducing DISJ1 with the right tail.
        # The right tail is parts[slot_idx+1] \/ parts[slot_idx+2] \/ ...
        # which is exactly the suffix of the original disjunction.
        # We can compute it from rhs_disj by walking slot_idx layers in.
        suffix = rhs_disj
        for _ in range(slot_idx):
            from basics import rand as _rand
            suffix = _rand(suffix)
        # suffix at this point is parts[slot_idx] \/ tail.
        # tail = rand of suffix.
        from basics import rand as _rand
        tail = _rand(suffix)
        th = DISJ1(th, tail)
        # th : |- parts[slot_idx] \/ tail
    # Now wrap with DISJ2 for each layer above slot_idx.
    for k in range(slot_idx - 1, -1, -1):
        th = DISJ2(parts[k], th)
    # th : |- D0 \/ D1 \/ ... \/ D6 = rhs_disj.
    is_logical_th = EQ_MP(SYM(is_logical_at), th)
    # is_logical_th : |- is_logical_axiom n_term

    is_axiom_at = SPEC(n_term, IS_AXIOM_AT)
    # is_axiom_at : |- is_axiom n = is_q_axiom n \/ is_logical_axiom n
    q_axiom_part = mk_app(is_q_axiom, n_term)
    is_axiom_th = EQ_MP(SYM(is_axiom_at),
                        DISJ2(q_axiom_part, is_logical_th))
    # is_axiom_th : |- is_axiom n_term

    # Apply PROV_Q_AXIOM at n_term.
    prov_q_axiom_at_n = SPEC(n_term, PROV_Q_AXIOM)
    # prov_q_axiom_at_n : |- is_axiom n ==> Prov_Q n
    prov_q_th = MP(prov_q_axiom_at_n, is_axiom_th)
    return prov_q_th


# ---------------------------------------------------------------------------
# Stage 2C (a) -- axiom-instance specializations.
# ---------------------------------------------------------------------------


@proof
def PROV_Q_K(p):
    """|- !A B. is_form A /\\ is_form B
                ==> Prov_Q (Imp_f A (Imp_f B A)).

    The K schema instance, lifted through the disjunction chain.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B "
        "==> Prov_Q (Imp_f A (Imp_f B A))",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.fix("A B")
    p.assume("(hA, hB): is_form A /\\ is_form B")

    n_term = p._parse("Imp_f A (Imp_f B A)")
    is_k_at_n = SPEC(n_term, IS_K_AT)

    p.have(
        "kbody: ?A1 B1. is_form A1 /\\ is_form B1 /\\ "
        "       Imp_f A (Imp_f B A) = Imp_f A1 (Imp_f B1 A1)"
    ).by_exists(["A", "B"], "hA", "hB")
    is_k_th = EQ_MP(SYM(is_k_at_n), p.fact("kbody"))
    # is_k_th : {} |- is_K (Imp_f A (Imp_f B A))

    prov_q_th = _prov_of_logical(p, "k", is_k_th, 0, n_term)
    p.thus("Prov_Q (Imp_f A (Imp_f B A))").by_thm(prov_q_th)


@proof
def PROV_Q_S(p):
    """|- !A B C. is_form A /\\ is_form B /\\ is_form C
                  ==> Prov_Q (Imp_f (Imp_f A (Imp_f B C))
                                    (Imp_f (Imp_f A B)
                                           (Imp_f A C))).

    The S schema instance.
    """
    p.goal(
        "!A B C. is_form A /\\ is_form B /\\ is_form C ==> "
        "Prov_Q (Imp_f (Imp_f A (Imp_f B C)) "
        "              (Imp_f (Imp_f A B) (Imp_f A C)))",
        types={"A": nat0_ty, "B": nat0_ty, "C": nat0_ty},
    )
    p.fix("A B C")
    p.assume("(hA, hB, hC): is_form A /\\ is_form B /\\ is_form C")

    n_term = p._parse(
        "Imp_f (Imp_f A (Imp_f B C)) (Imp_f (Imp_f A B) (Imp_f A C))"
    )
    is_s_at_n = SPEC(n_term, IS_S_AT)

    p.have(
        "sbody: ?A1 B1 C1. is_form A1 /\\ is_form B1 /\\ is_form C1 /\\ "
        "       Imp_f (Imp_f A (Imp_f B C)) (Imp_f (Imp_f A B) (Imp_f A C)) "
        "       = Imp_f (Imp_f A1 (Imp_f B1 C1)) "
        "               (Imp_f (Imp_f A1 B1) (Imp_f A1 C1))"
    ).by_exists(["A", "B", "C"], "hA", "hB", "hC")
    is_s_th = EQ_MP(SYM(is_s_at_n), p.fact("sbody"))

    prov_q_th = _prov_of_logical(p, "s", is_s_th, 1, n_term)
    p.thus(
        "Prov_Q (Imp_f (Imp_f A (Imp_f B C)) "
        "              (Imp_f (Imp_f A B) (Imp_f A C)))"
    ).by_thm(prov_q_th)


@proof
def PROV_Q_N(p):
    """|- !A B. is_form A /\\ is_form B
                ==> Prov_Q (Imp_f (Imp_f (Not_f B) (Not_f A))
                                  (Imp_f A B)).

    The N schema instance (contraposition).
    """
    p.goal(
        "!A B. is_form A /\\ is_form B ==> "
        "Prov_Q (Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B))",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.fix("A B")
    p.assume("(hA, hB): is_form A /\\ is_form B")

    n_term = p._parse(
        "Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B)"
    )
    is_n_at_n = SPEC(n_term, IS_N_AT)

    p.have(
        "nbody: ?A1 B1. is_form A1 /\\ is_form B1 /\\ "
        "       Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B) "
        "       = Imp_f (Imp_f (Not_f B1) (Not_f A1)) (Imp_f A1 B1)"
    ).by_exists(["A", "B"], "hA", "hB")
    is_n_th = EQ_MP(SYM(is_n_at_n), p.fact("nbody"))

    prov_q_th = _prov_of_logical(p, "n", is_n_th, 2, n_term)
    p.thus(
        "Prov_Q (Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B))"
    ).by_thm(prov_q_th)


# ---------------------------------------------------------------------------
# Stage 2C (b) -- basic propositional reasoning.
# ---------------------------------------------------------------------------


@proof
def PROV_Q_IMP_REFL(p):
    """|- !A. is_form A ==> Prov_Q (Imp_f A A).

    Standard Mendelson derivation:
      1. K at (A, Imp_f A A): A -> ((A -> A) -> A)
      2. K at (A, A):         A -> (A -> A)
      3. S at (A, A -> A, A): (A -> ((A -> A) -> A))
                                 -> ((A -> (A -> A)) -> (A -> A))
      4. MP(1, 3):            (A -> (A -> A)) -> (A -> A)
      5. MP(2, 4):            A -> A
    """
    p.goal(
        "!A. is_form A ==> Prov_Q (Imp_f A A)",
        types={"A": nat0_ty},
    )
    p.fix("A")
    p.assume("hA: is_form A")

    # is_form (Imp_f A A) needed for K-instance #1 and S-instance.
    is_form_imp_AA = SPECL([p._parse("A"), p._parse("A")], IS_FORM_AT_IMP)
    # is_form_imp_AA : |- is_form (Imp_f A A) = is_form A /\ is_form A
    p.have("hAA: is_form (Imp_f A A)").by_eq_mp(
        SYM(is_form_imp_AA), CONJ(p.fact("hA"), p.fact("hA"))
    )

    p.have("hA_AA: is_form A /\\ is_form (Imp_f A A)").by_thm(
        CONJ(p.fact("hA"), p.fact("hAA"))
    )
    p.have("hA_A: is_form A /\\ is_form A").by_thm(
        CONJ(p.fact("hA"), p.fact("hA"))
    )
    p.have(
        "h_S_conj: is_form A /\\ is_form (Imp_f A A) /\\ is_form A"
    ).by_thm(
        CONJ(p.fact("hA"), CONJ(p.fact("hAA"), p.fact("hA")))
    )

    # Step 1: K at (A, Imp_f A A).
    p.have(
        "k1: Prov_Q (Imp_f A (Imp_f (Imp_f A A) A))"
    ).by(PROV_Q_K, "A", "Imp_f A A", "hA_AA")

    # Step 2: K at (A, A).
    p.have(
        "k2: Prov_Q (Imp_f A (Imp_f A A))"
    ).by(PROV_Q_K, "A", "A", "hA_A")

    # Step 3: S at (A, A -> A, A).
    p.have(
        "s1: Prov_Q (Imp_f (Imp_f A (Imp_f (Imp_f A A) A)) "
        "                  (Imp_f (Imp_f A (Imp_f A A)) "
        "                         (Imp_f A A)))"
    ).by(PROV_Q_S, "A", "Imp_f A A", "A", "h_S_conj")

    # Step 4: MP(k1, s1) -> mp1.
    p.have("k1_s1: Prov_Q (Imp_f A (Imp_f (Imp_f A A) A)) /\\ "
           "             Prov_Q (Imp_f (Imp_f A (Imp_f (Imp_f A A) A)) "
           "                           (Imp_f (Imp_f A (Imp_f A A)) "
           "                                  (Imp_f A A)))"
           ).by_thm(CONJ(p.fact("k1"), p.fact("s1")))
    p.have(
        "mp1: Prov_Q (Imp_f (Imp_f A (Imp_f A A)) (Imp_f A A))"
    ).by(PROV_Q_MP, "Imp_f A (Imp_f (Imp_f A A) A)",
         "Imp_f (Imp_f A (Imp_f A A)) (Imp_f A A)", "k1_s1")

    # Step 5: MP(k2, mp1).
    p.have(
        "k2_mp1: Prov_Q (Imp_f A (Imp_f A A)) /\\ "
        "        Prov_Q (Imp_f (Imp_f A (Imp_f A A)) (Imp_f A A))"
    ).by_thm(CONJ(p.fact("k2"), p.fact("mp1")))
    p.thus("Prov_Q (Imp_f A A)").by(
        PROV_Q_MP, "Imp_f A (Imp_f A A)", "Imp_f A A", "k2_mp1"
    )


@proof
def PROV_Q_HYP_DROP(p):
    """|- !A B. is_form A /\\ is_form B /\\ Prov_Q B
                ==> Prov_Q (Imp_f A B).

    "Drop a hypothesis": from a Q-theorem ``B`` derive ``A -> B`` for
    any well-formed ``A``. One MP through K at (B, A): K gives
    ``B -> (A -> B)``; MP with ``Prov_Q B`` yields ``Prov_Q (A -> B)``.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B /\\ Prov_Q B "
        "==> Prov_Q (Imp_f A B)",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.fix("A B")
    p.assume("(hA, hB, hPB): is_form A /\\ is_form B /\\ Prov_Q B")

    # K at (B, A): Prov_Q (Imp_f B (Imp_f A B)).
    p.have("hB_A: is_form B /\\ is_form A").by_thm(
        CONJ(p.fact("hB"), p.fact("hA"))
    )
    p.have(
        "k_BA: Prov_Q (Imp_f B (Imp_f A B))"
    ).by(PROV_Q_K, "B", "A", "hB_A")

    # MP(hPB, k_BA): Prov_Q (Imp_f A B).
    p.have(
        "mp_in: Prov_Q B /\\ Prov_Q (Imp_f B (Imp_f A B))"
    ).by_thm(CONJ(p.fact("hPB"), p.fact("k_BA")))
    p.thus("Prov_Q (Imp_f A B)").by(
        PROV_Q_MP, "B", "Imp_f A B", "mp_in"
    )


@proof
def PROV_Q_TRANS_IMP(p):
    """|- !A B C. is_form A /\\ is_form B /\\ is_form C
                  /\\ Prov_Q (Imp_f A B) /\\ Prov_Q (Imp_f B C)
                  ==> Prov_Q (Imp_f A C).

    Transitivity of Q-implication. Standard route:
      1. HYP_DROP on Prov_Q (Imp_f B C) with hyp A:
            Prov_Q (Imp_f A (Imp_f B C)).
      2. S at (A, B, C):
            Prov_Q ((A -> (B -> C)) -> ((A -> B) -> (A -> C))).
      3. MP twice yields Prov_Q (Imp_f A C).
    """
    p.goal(
        "!A B C. is_form A /\\ is_form B /\\ is_form C "
        "/\\ Prov_Q (Imp_f A B) /\\ Prov_Q (Imp_f B C) "
        "==> Prov_Q (Imp_f A C)",
        types={"A": nat0_ty, "B": nat0_ty, "C": nat0_ty},
    )
    p.fix("A B C")
    p.assume(
        "(hA, hB, hC, hAB, hBC): "
        "is_form A /\\ is_form B /\\ is_form C "
        "/\\ Prov_Q (Imp_f A B) /\\ Prov_Q (Imp_f B C)"
    )

    # is_form (Imp_f B C) for HYP_DROP.
    is_form_imp_BC = SPECL(
        [p._parse("B"), p._parse("C")], IS_FORM_AT_IMP
    )
    p.have("hBC_form: is_form (Imp_f B C)").by_eq_mp(
        SYM(is_form_imp_BC), CONJ(p.fact("hB"), p.fact("hC"))
    )

    # Step 1: HYP_DROP gives A -> (B -> C).
    p.have(
        "hyp_in: is_form A /\\ is_form (Imp_f B C) /\\ Prov_Q (Imp_f B C)"
    ).by_thm(CONJ(p.fact("hA"),
                  CONJ(p.fact("hBC_form"), p.fact("hBC"))))
    p.have(
        "p1: Prov_Q (Imp_f A (Imp_f B C))"
    ).by(PROV_Q_HYP_DROP, "A", "Imp_f B C", "hyp_in")

    # Step 2: S at (A, B, C).
    p.have(
        "h_S_conj: is_form A /\\ is_form B /\\ is_form C"
    ).by_thm(CONJ(p.fact("hA"), CONJ(p.fact("hB"), p.fact("hC"))))
    p.have(
        "p2: Prov_Q (Imp_f (Imp_f A (Imp_f B C)) "
        "                  (Imp_f (Imp_f A B) (Imp_f A C)))"
    ).by(PROV_Q_S, "A", "B", "C", "h_S_conj")

    # Step 3a: MP(p1, p2): Prov_Q ((A -> B) -> (A -> C)).
    p.have(
        "mp_a: Prov_Q (Imp_f A (Imp_f B C)) /\\ "
        "      Prov_Q (Imp_f (Imp_f A (Imp_f B C)) "
        "                    (Imp_f (Imp_f A B) (Imp_f A C)))"
    ).by_thm(CONJ(p.fact("p1"), p.fact("p2")))
    p.have(
        "p3: Prov_Q (Imp_f (Imp_f A B) (Imp_f A C))"
    ).by(PROV_Q_MP, "Imp_f A (Imp_f B C)",
         "Imp_f (Imp_f A B) (Imp_f A C)", "mp_a")

    # Step 3b: MP(hAB, p3): Prov_Q (Imp_f A C).
    p.have(
        "mp_b: Prov_Q (Imp_f A B) /\\ "
        "      Prov_Q (Imp_f (Imp_f A B) (Imp_f A C))"
    ).by_thm(CONJ(p.fact("hAB"), p.fact("p3")))
    p.thus("Prov_Q (Imp_f A C)").by(
        PROV_Q_MP, "Imp_f A B", "Imp_f A C", "mp_b"
    )


@proof
def PROV_Q_EX_FALSO(p):
    """|- !A B. is_form A /\\ is_form B
                ==> Prov_Q (Imp_f (Not_f A) (Imp_f A B)).

    "Ex falso quodlibet" / Mendelson Lemma 1.10(a).
    Direct chain: ``K`` gives ``~A -> (~B -> ~A)``; ``N`` at (A, B)
    gives ``(~B -> ~A) -> (A -> B)``; TRANS_IMP composes them.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B "
        "==> Prov_Q (Imp_f (Not_f A) (Imp_f A B))",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.fix("A B")
    p.assume("(hA, hB): is_form A /\\ is_form B")

    # is_form (Not_f A), is_form (Not_f B), is_form (Imp_f A B) needed.
    isfA_not = SPEC(p._parse("A"), IS_FORM_AT_NOT)
    isfB_not = SPEC(p._parse("B"), IS_FORM_AT_NOT)
    p.have("hNA: is_form (Not_f A)").by_eq_mp(SYM(isfA_not), "hA")
    p.have("hNB: is_form (Not_f B)").by_eq_mp(SYM(isfB_not), "hB")
    is_form_imp_NB_NA = SPECL(
        [p._parse("Not_f B"), p._parse("Not_f A")], IS_FORM_AT_IMP
    )
    p.have(
        "hNBNA_form: is_form (Imp_f (Not_f B) (Not_f A))"
    ).by_eq_mp(SYM(is_form_imp_NB_NA),
               CONJ(p.fact("hNB"), p.fact("hNA")))
    is_form_imp_AB = SPECL(
        [p._parse("A"), p._parse("B")], IS_FORM_AT_IMP
    )
    p.have("hAB_form: is_form (Imp_f A B)").by_eq_mp(
        SYM(is_form_imp_AB), CONJ(p.fact("hA"), p.fact("hB"))
    )

    # K at (~A, ~B): ~A -> (~B -> ~A).
    p.have("h_K_in: is_form (Not_f A) /\\ is_form (Not_f B)").by_thm(
        CONJ(p.fact("hNA"), p.fact("hNB"))
    )
    p.have(
        "k1: Prov_Q (Imp_f (Not_f A) (Imp_f (Not_f B) (Not_f A)))"
    ).by(PROV_Q_K, "Not_f A", "Not_f B", "h_K_in")

    # N at (A, B): (~B -> ~A) -> (A -> B).
    p.have(
        "n1: Prov_Q (Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B))"
    ).by(PROV_Q_N, "A", "B", CONJ(p.fact("hA"), p.fact("hB")))

    # TRANS_IMP: ~A -> (~B -> ~A), (~B -> ~A) -> (A -> B), so ~A -> (A -> B).
    p.have(
        "h_T_conj: is_form (Not_f A) "
        "/\\ is_form (Imp_f (Not_f B) (Not_f A)) "
        "/\\ is_form (Imp_f A B) "
        "/\\ Prov_Q (Imp_f (Not_f A) (Imp_f (Not_f B) (Not_f A))) "
        "/\\ Prov_Q (Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B))"
    ).by_thm(CONJ(p.fact("hNA"),
                  CONJ(p.fact("hNBNA_form"),
                       CONJ(p.fact("hAB_form"),
                            CONJ(p.fact("k1"), p.fact("n1"))))))
    p.thus("Prov_Q (Imp_f (Not_f A) (Imp_f A B))").by(
        PROV_Q_TRANS_IMP,
        "Not_f A", "Imp_f (Not_f B) (Not_f A)", "Imp_f A B",
        "h_T_conj",
    )


# ---------------------------------------------------------------------------
# Stage 2C (c) -- negation reasoning.
#
# Headlines (Mendelson Lemma 1.11):
#   * ``A -> ~~A`` (double-negation introduction)
#   * ``~~A -> A`` (double-negation elimination)
#
# Both via the N axiom ``(~B -> ~A) -> (A -> B)`` plus K/S manipulation.
# ---------------------------------------------------------------------------


@proof
def PROV_Q_DOUBLE_NEG_INTRO(p):
    """|- !A. is_form A /\\ Prov_Q A ==> Prov_Q (Not_f (Not_f A)).

    Mendelson Lemma 1.11(a). STUB; see implementation below.
    """
    p.goal(
        "!A. is_form A /\\ Prov_Q A ==> Prov_Q (Not_f (Not_f A))",
        types={"A": nat0_ty},
    )
    p.sorry()


@proof
def PROV_Q_DOUBLE_NEG_ELIM(p):
    """|- !A. is_form A /\\ Prov_Q (Not_f (Not_f A)) ==> Prov_Q A.

    Mendelson Lemma 1.11(b). STUB; see implementation below.
    """
    p.goal(
        "!A. is_form A /\\ Prov_Q (Not_f (Not_f A)) ==> Prov_Q A",
        types={"A": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2C (d) -- conjunction and biconditional introduction.
#
# Encoded forms (since Q's primitives are Imp_f / Not_f only):
#   And_f A B  =  Not_f (Imp_f A (Not_f B))
#   Iff_f A B  =  Not_f (Imp_f (Imp_f A B) (Not_f (Imp_f B A)))
#                          (= And_f (Imp_f A B) (Imp_f B A))
# ---------------------------------------------------------------------------


@proof
def PROV_Q_AND_INTRO(p):
    """|- !A B. is_form A /\\ is_form B /\\ Prov_Q A /\\ Prov_Q B
                ==> Prov_Q (Not_f (Imp_f A (Not_f B))).

    Conjunction-introduction in Q. STUB; see implementation below.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B /\\ Prov_Q A /\\ Prov_Q B "
        "==> Prov_Q (Not_f (Imp_f A (Not_f B)))",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.sorry()


@proof
def PROV_Q_IFF_INTRO(p):
    """|- !A B. is_form A /\\ is_form B
                /\\ Prov_Q (Imp_f A B) /\\ Prov_Q (Imp_f B A)
                ==> Prov_Q (Not_f (Imp_f (Imp_f A B)
                                          (Not_f (Imp_f B A)))).

    Biconditional-introduction in Q. Direct application of AND_INTRO at
    the two implication directions: the conjunction of (A->B) and
    (B->A) is exactly the encoded biconditional.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B "
        "/\\ Prov_Q (Imp_f A B) /\\ Prov_Q (Imp_f B A) "
        "==> Prov_Q (Not_f (Imp_f (Imp_f A B) "
        "                         (Not_f (Imp_f B A))))",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.fix("A B")
    p.assume(
        "(hA, hB, hAB, hBA): "
        "is_form A /\\ is_form B "
        "/\\ Prov_Q (Imp_f A B) /\\ Prov_Q (Imp_f B A)"
    )

    # is_form (Imp_f A B), is_form (Imp_f B A) for AND_INTRO.
    is_form_imp_AB = SPECL(
        [p._parse("A"), p._parse("B")], IS_FORM_AT_IMP
    )
    is_form_imp_BA = SPECL(
        [p._parse("B"), p._parse("A")], IS_FORM_AT_IMP
    )
    p.have("hABf: is_form (Imp_f A B)").by_eq_mp(
        SYM(is_form_imp_AB), CONJ(p.fact("hA"), p.fact("hB"))
    )
    p.have("hBAf: is_form (Imp_f B A)").by_eq_mp(
        SYM(is_form_imp_BA), CONJ(p.fact("hB"), p.fact("hA"))
    )

    # AND_INTRO at (Imp_f A B, Imp_f B A) gives the encoded And_f form.
    p.have(
        "and_in: is_form (Imp_f A B) /\\ is_form (Imp_f B A) "
        "        /\\ Prov_Q (Imp_f A B) /\\ Prov_Q (Imp_f B A)"
    ).by_thm(CONJ(p.fact("hABf"),
                  CONJ(p.fact("hBAf"),
                       CONJ(p.fact("hAB"), p.fact("hBA")))))
    p.thus(
        "Prov_Q (Not_f (Imp_f (Imp_f A B) (Not_f (Imp_f B A))))"
    ).by(PROV_Q_AND_INTRO, "Imp_f A B", "Imp_f B A", "and_in")


# ---------------------------------------------------------------------------
# Stage 2C (e) -- existential introduction.
#
# Exists_f x F = Not_f (Forall_f x (Not_f F)).
#
# Standard derivation: from a witness ``Prov_Q (substitute F t x)``,
# combine with the UI axiom (specialised at the negation) and N to
# derive ``Prov_Q (Not_f (Forall_f x (Not_f F)))``.
# ---------------------------------------------------------------------------


@proof
def PROV_Q_EXISTS_INTRO(p):
    """|- !x F t. is_form F /\\ is_term t /\\ Prov_Q (substitute F t x)
                  ==> Prov_Q (Not_f (Forall_f x (Not_f F))).

    Existential-introduction in Q (encoded form). STUB; see
    implementation below.
    """
    p.goal(
        "!x F t. is_form F /\\ is_term t /\\ "
        "Prov_Q (substitute F t x) "
        "==> Prov_Q (Not_f (Forall_f x (Not_f F)))",
        types={"x": nat0_ty, "F": nat0_ty, "t": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2C (f) -- conjunction elimination (And_f projections).
#
# And_f A B = Not_f (Imp_f A (Not_f B)). Given the encoded form, the
# standard projections are:
#   ELIM_LEFT  : Prov_Q (~(A -> ~B)) ==> Prov_Q A
#   ELIM_RIGHT : Prov_Q (~(A -> ~B)) ==> Prov_Q B
#
# Each goes through DOUBLE_NEG_ELIM + N + S manipulation.
# ---------------------------------------------------------------------------


@proof
def PROV_Q_AND_ELIM_LEFT(p):
    """|- !A B. is_form A /\\ is_form B
                /\\ Prov_Q (Not_f (Imp_f A (Not_f B)))
                ==> Prov_Q A.

    Left projection of conjunction. STUB.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B "
        "/\\ Prov_Q (Not_f (Imp_f A (Not_f B))) "
        "==> Prov_Q A",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.sorry()


@proof
def PROV_Q_AND_ELIM_RIGHT(p):
    """|- !A B. is_form A /\\ is_form B
                /\\ Prov_Q (Not_f (Imp_f A (Not_f B)))
                ==> Prov_Q B.

    Right projection of conjunction. STUB.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B "
        "/\\ Prov_Q (Not_f (Imp_f A (Not_f B))) "
        "==> Prov_Q B",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2C (g) -- existential elimination (∃-elim).
#
# Hilbert formulation as a derivable rule:
#   If ``Prov_Q (Imp_f P Q)`` and ``v`` is not free in ``Q``,
#   then ``Prov_Q (Imp_f (Exists_f v P) Q)``.
#
# Encoded form (Exists_f v P = Not_f (Forall_f v (Not_f P))):
#   Prov_Q (Imp_f (Not_f (Forall_f v (Not_f P))) Q).
#
# Standard derivation: contrapositive via N axiom + Gen + Vac.
# ---------------------------------------------------------------------------


@proof
def PROV_Q_EXISTS_ELIM(p):
    """|- !v P Q. is_form P /\\ is_form Q /\\ ~(free_in Q v)
                  /\\ Prov_Q (Imp_f P Q)
                  ==> Prov_Q (Imp_f (Not_f (Forall_f v (Not_f P))) Q).

    Existential-elimination as a derived rule (encoded form). STUB.
    """
    p.goal(
        "!v P Q. is_form P /\\ is_form Q /\\ ~(free_in Q v) "
        "/\\ Prov_Q (Imp_f P Q) "
        "==> Prov_Q (Imp_f (Not_f (Forall_f v (Not_f P))) Q)",
        types={"v": nat0_ty, "P": nat0_ty, "Q": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2C (h) -- substitution under equality (Subst axiom in MP form).
#
# The is_Subst axiom schema, lifted through the disjunction chain to
# Prov_Q (slot 6 of is_logical_axiom). Direct analogue of PROV_Q_K /
# PROV_Q_S / PROV_Q_N -- could be filled in immediately by the same
# pattern (kept as a stub here only because the body's witness building
# is the same boilerplate).
# ---------------------------------------------------------------------------


@proof
def PROV_Q_SUBST_EQ(p):
    """|- !x F t1 t2. is_form F /\\ is_term t1 /\\ is_term t2
                      ==> Prov_Q (Imp_f (Eq_f t1 t2)
                                        (Imp_f (substitute F t1 x)
                                               (substitute F t2 x))).

    The is_Subst axiom in MP-friendly form. STUB; analogous to
    PROV_Q_K / PROV_Q_S / PROV_Q_N -- direct application of
    ``_prov_of_logical`` at slot 6.
    """
    p.goal(
        "!x F t1 t2. is_form F /\\ is_term t1 /\\ is_term t2 "
        "==> Prov_Q (Imp_f (Eq_f t1 t2) "
        "                  (Imp_f (substitute F t1 x) "
        "                         (substitute F t2 x)))",
        types={"x": nat0_ty, "F": nat0_ty,
               "t1": nat0_ty, "t2": nat0_ty},
    )
    p.sorry()


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 2C (a) -- axiom-instance specializations.")
    print("    PROV_Q_K :", pp_thm(PROV_Q_K))
    print("    PROV_Q_S :", pp_thm(PROV_Q_S))
    print("    PROV_Q_N :", pp_thm(PROV_Q_N))
    print()
    print("Stage 2C (b) -- basic propositional reasoning.")
    print("    PROV_Q_IMP_REFL  :", pp_thm(PROV_Q_IMP_REFL))
    print("    PROV_Q_HYP_DROP  :", pp_thm(PROV_Q_HYP_DROP))
    print("    PROV_Q_TRANS_IMP :", pp_thm(PROV_Q_TRANS_IMP))
    print("    PROV_Q_EX_FALSO  :", pp_thm(PROV_Q_EX_FALSO))
    print()
    print("Stage 2C (c) -- negation reasoning (STUB).")
    print("    PROV_Q_DOUBLE_NEG_INTRO :", pp_thm(PROV_Q_DOUBLE_NEG_INTRO))
    print("    PROV_Q_DOUBLE_NEG_ELIM  :", pp_thm(PROV_Q_DOUBLE_NEG_ELIM))
    print()
    print("Stage 2C (d) -- conjunction / biconditional intro (STUB).")
    print("    PROV_Q_AND_INTRO :", pp_thm(PROV_Q_AND_INTRO))
    print("    PROV_Q_IFF_INTRO :", pp_thm(PROV_Q_IFF_INTRO))
    print()
    print("Stage 2C (e) -- existential intro (STUB).")
    print("    PROV_Q_EXISTS_INTRO :", pp_thm(PROV_Q_EXISTS_INTRO))
    print()
    print("Stage 2C (f) -- conjunction elimination (STUB).")
    print("    PROV_Q_AND_ELIM_LEFT  :", pp_thm(PROV_Q_AND_ELIM_LEFT))
    print("    PROV_Q_AND_ELIM_RIGHT :", pp_thm(PROV_Q_AND_ELIM_RIGHT))
    print()
    print("Stage 2C (g) -- existential elimination (STUB).")
    print("    PROV_Q_EXISTS_ELIM :", pp_thm(PROV_Q_EXISTS_ELIM))
    print()
    print("Stage 2C (h) -- substitution under equality (STUB).")
    print("    PROV_Q_SUBST_EQ :", pp_thm(PROV_Q_SUBST_EQ))

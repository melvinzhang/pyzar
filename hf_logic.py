# ---------------------------------------------------------------------------
# Stage 2C -- HF-internal logic.
# ---------------------------------------------------------------------------
#
# Build first-order logical reasoning *inside* HF from the seven axiom
# schemas (K, S, N, UI, Vac, Refl, Subst) plus MP and Gen. Each lemma
# in this file derives a standard meta-theorem -- "HF proves X" -- as a
# HOL theorem about ``Prov_HF``.
#
# Layered build-up:
#
#   (a) axiom-instance specializations      PROV_HF_K, PROV_HF_S, PROV_HF_N
#   (b) basic propositional reasoning       PROV_HF_IMP_REFL,
#                                           PROV_HF_HYP_DROP,
#                                           PROV_HF_TRANS_IMP
#   (c) conjunction / iff                   PROV_HF_AND_INTRO,
#                                           PROV_HF_IFF_INTRO
#
# Consumed by the diagonal lemma (Stage 4) and the Goedel-sentence main
# theorem (Stage 5).
# ---------------------------------------------------------------------------


from basics import mk_app, rand, aconv
from nat0 import nat0_ty
from proof import proof
from tactics import (
    SPEC,
    SPECL,
    MP,
    CONJ,
    DISJ1,
    DISJ2,
    EQ_MP,
    SYM,
)

from hf_syntax import (
    IS_FORM_AT_IMP,
    IS_FORM_AT_NOT,
)
from hf_proof import (
    IS_K_AT,
    IS_S_AT,
    IS_N_AT,
    IS_UI_AT,
    is_hf_axiom,
    IS_LOGICAL_AXIOM_AT,
    IS_AXIOM_AT,
)
from hf_repr import (
    PROV_HF_AXIOM,
    PROV_HF_MP,
)


# ---------------------------------------------------------------------------
# Helper: lift ``|- is_K n`` (or is_S / is_N) through the disjunction
# chain into ``|- Prov_HF n``.
#
# Chain:  is_<X> n  ->  is_logical_axiom n  ->  is_axiom n  ->  Prov_HF n.
#
# is_<X> sits as one disjunct in IS_LOGICAL_AXIOM_AT's right-associated
# 7-way OR. is_logical_axiom sits as the right disjunct of IS_AXIOM_AT.
# Caller specifies which logical-axiom slot via ``slot``: 0=K, 1=S,
# 2=N, 3=UI, 4=Vac, 5=Refl, 6=Subst.
# ---------------------------------------------------------------------------


def _prov_of_logical(p, name, slot_th, slot_idx, n_term):
    """Lift ``slot_th : {} |- is_<X> n_term`` to ``|- Prov_HF n_term``.

    Posts intermediate facts ``{name}_logical`` and ``{name}_axiom``
    in scope; returns the final Prov_HF theorem (also posted under
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
    # is_axiom_at : |- is_axiom n = is_hf_axiom n \/ is_logical_axiom n
    q_axiom_part = mk_app(is_hf_axiom, n_term)
    is_axiom_th = EQ_MP(SYM(is_axiom_at), DISJ2(q_axiom_part, is_logical_th))
    # is_axiom_th : |- is_axiom n_term

    # Apply PROV_HF_AXIOM at n_term.
    prov_q_axiom_at_n = SPEC(n_term, PROV_HF_AXIOM)
    # prov_q_axiom_at_n : |- is_axiom n ==> Prov_HF n
    prov_q_th = MP(prov_q_axiom_at_n, is_axiom_th)
    return prov_q_th


# ---------------------------------------------------------------------------
# Stage 2C (a) -- axiom-instance specializations.
# ---------------------------------------------------------------------------


@proof
def PROV_HF_K(p):
    """|- !A B. is_form A /\\ is_form B
                ==> Prov_HF (Imp_f A (Imp_f B A)).

    The K schema instance, lifted through the disjunction chain.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B ==> Prov_HF (Imp_f A (Imp_f B A))",
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
    p.thus("Prov_HF (Imp_f A (Imp_f B A))").by_thm(prov_q_th)


@proof
def PROV_HF_S(p):
    """|- !A B C. is_form A /\\ is_form B /\\ is_form C
                  ==> Prov_HF (Imp_f (Imp_f A (Imp_f B C))
                                    (Imp_f (Imp_f A B)
                                           (Imp_f A C))).

    The S schema instance.
    """
    p.goal(
        "!A B C. is_form A /\\ is_form B /\\ is_form C ==> "
        "Prov_HF (Imp_f (Imp_f A (Imp_f B C)) "
        "              (Imp_f (Imp_f A B) (Imp_f A C)))",
        types={"A": nat0_ty, "B": nat0_ty, "C": nat0_ty},
    )
    p.fix("A B C")
    p.assume("(hA, hB, hC): is_form A /\\ is_form B /\\ is_form C")

    n_term = p._parse("Imp_f (Imp_f A (Imp_f B C)) (Imp_f (Imp_f A B) (Imp_f A C))")
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
        "Prov_HF (Imp_f (Imp_f A (Imp_f B C)) "
        "              (Imp_f (Imp_f A B) (Imp_f A C)))"
    ).by_thm(prov_q_th)


@proof
def PROV_HF_N(p):
    """|- !A B. is_form A /\\ is_form B
                ==> Prov_HF (Imp_f (Imp_f (Not_f B) (Not_f A))
                                  (Imp_f A B)).

    The N schema instance (contraposition).
    """
    p.goal(
        "!A B. is_form A /\\ is_form B ==> "
        "Prov_HF (Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B))",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.fix("A B")
    p.assume("(hA, hB): is_form A /\\ is_form B")

    n_term = p._parse("Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B)")
    is_n_at_n = SPEC(n_term, IS_N_AT)

    p.have(
        "nbody: ?A1 B1. is_form A1 /\\ is_form B1 /\\ "
        "       Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B) "
        "       = Imp_f (Imp_f (Not_f B1) (Not_f A1)) (Imp_f A1 B1)"
    ).by_exists(["A", "B"], "hA", "hB")
    is_n_th = EQ_MP(SYM(is_n_at_n), p.fact("nbody"))

    prov_q_th = _prov_of_logical(p, "n", is_n_th, 2, n_term)
    p.thus("Prov_HF (Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B))").by_thm(prov_q_th)


# ---------------------------------------------------------------------------
# Stage 2C (a') -- universal instantiation as a derived rule.
#
# Given ``Prov_HF (Forall_f x F)``, the UI logical-axiom schema (slot 3)
# witnesses ``Prov_HF (Imp_f (Forall_f x F) (substitute F t x))`` for any
# term ``t`` and form ``F``; one MP yields ``Prov_HF (substitute F t x)``.
# Required for instantiating closed HF1-HF5 axioms at concrete arguments.
# ---------------------------------------------------------------------------


@proof
def PROV_HF_UI(p):
    """|- !x phi t. is_form phi /\\ is_term t /\\ Prov_HF (Forall_f x phi)
                    ==> Prov_HF (substitute phi t x).

    Universal instantiation. Witnesses (x, phi, t) into the is_UI body
    schema, lifts the resulting ``is_UI (Imp_f (Forall_f x phi) ...)`` to
    Prov_HF via ``_prov_of_logical`` at slot 3, then PROV_HF_MP discharges
    the implication using the supplied ``Prov_HF (Forall_f x phi)``.

    DSL friction note (dsl_spec.md cross-ref): the goal text uses ``phi``
    rather than ``F`` because ``F`` is the kernel False constant
    (``from axioms import F``) and the parser preferentially resolves bare
    ``F`` to the constant rather than a fresh binder, even with
    ``types={"F": nat0_ty}`` declared.
    """
    p.goal(
        "!x phi t. is_form phi /\\ is_term t /\\ Prov_HF (Forall_f x phi) "
        "==> Prov_HF (substitute phi t x)",
        types={"x": nat0_ty, "phi": nat0_ty, "t": nat0_ty},
    )
    p.fix("x phi t")
    p.assume(
        "(hphi, ht, hPF): is_form phi /\\ is_term t /\\ Prov_HF (Forall_f x phi)"
    )

    n_term = p._parse("Imp_f (Forall_f x phi) (substitute phi t x)")
    is_ui_at_n = SPEC(n_term, IS_UI_AT)

    # Witness ?x1 phi1 t1. is_form phi1 /\ is_term t1 /\ n_term = ...
    p.have(
        "ui_body: ?x1 phi1 t1. is_form phi1 /\\ is_term t1 /\\ "
        "       Imp_f (Forall_f x phi) (substitute phi t x) "
        "       = Imp_f (Forall_f x1 phi1) (substitute phi1 t1 x1)"
    ).by_exists(["x", "phi", "t"], "hphi", "ht")
    is_ui_th = EQ_MP(SYM(is_ui_at_n), p.fact("ui_body"))
    # is_ui_th : |- is_UI (Imp_f (Forall_f x phi) (substitute phi t x))

    prov_imp = _prov_of_logical(p, "ui", is_ui_th, 3, n_term)
    # prov_imp : |- Prov_HF (Imp_f (Forall_f x phi) (substitute phi t x))

    p.have(
        "h_mp_in: Prov_HF (Forall_f x phi) /\\ "
        "         Prov_HF (Imp_f (Forall_f x phi) (substitute phi t x))"
    ).by_thm(CONJ(p.fact("hPF"), prov_imp))
    p.thus("Prov_HF (substitute phi t x)").by(
        PROV_HF_MP, "Forall_f x phi", "substitute phi t x", "h_mp_in"
    )


# ---------------------------------------------------------------------------
# Stage 2C (b) -- basic propositional reasoning.
# ---------------------------------------------------------------------------


@proof
def PROV_HF_IMP_REFL(p):
    """|- !A. is_form A ==> Prov_HF (Imp_f A A).

    Standard Mendelson derivation:
      1. K at (A, Imp_f A A): A -> ((A -> A) -> A)
      2. K at (A, A):         A -> (A -> A)
      3. S at (A, A -> A, A): (A -> ((A -> A) -> A))
                                 -> ((A -> (A -> A)) -> (A -> A))
      4. MP(1, 3):            (A -> (A -> A)) -> (A -> A)
      5. MP(2, 4):            A -> A
    """
    p.goal(
        "!A. is_form A ==> Prov_HF (Imp_f A A)",
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
    p.have("hA_A: is_form A /\\ is_form A").by_thm(CONJ(p.fact("hA"), p.fact("hA")))
    p.have("h_S_conj: is_form A /\\ is_form (Imp_f A A) /\\ is_form A").by_thm(
        CONJ(p.fact("hA"), CONJ(p.fact("hAA"), p.fact("hA")))
    )

    # Step 1: K at (A, Imp_f A A).
    p.have("k1: Prov_HF (Imp_f A (Imp_f (Imp_f A A) A))").by(
        PROV_HF_K, "A", "Imp_f A A", "hA_AA"
    )

    # Step 2: K at (A, A).
    p.have("k2: Prov_HF (Imp_f A (Imp_f A A))").by(PROV_HF_K, "A", "A", "hA_A")

    # Step 3: S at (A, A -> A, A).
    p.have(
        "s1: Prov_HF (Imp_f (Imp_f A (Imp_f (Imp_f A A) A)) "
        "                  (Imp_f (Imp_f A (Imp_f A A)) "
        "                         (Imp_f A A)))"
    ).by(PROV_HF_S, "A", "Imp_f A A", "A", "h_S_conj")

    # Step 4: MP(k1, s1) -> mp1.
    p.have(
        "k1_s1: Prov_HF (Imp_f A (Imp_f (Imp_f A A) A)) /\\ "
        "             Prov_HF (Imp_f (Imp_f A (Imp_f (Imp_f A A) A)) "
        "                           (Imp_f (Imp_f A (Imp_f A A)) "
        "                                  (Imp_f A A)))"
    ).by_thm(CONJ(p.fact("k1"), p.fact("s1")))
    p.have("mp1: Prov_HF (Imp_f (Imp_f A (Imp_f A A)) (Imp_f A A))").by(
        PROV_HF_MP,
        "Imp_f A (Imp_f (Imp_f A A) A)",
        "Imp_f (Imp_f A (Imp_f A A)) (Imp_f A A)",
        "k1_s1",
    )

    # Step 5: MP(k2, mp1).
    p.have(
        "k2_mp1: Prov_HF (Imp_f A (Imp_f A A)) /\\ "
        "        Prov_HF (Imp_f (Imp_f A (Imp_f A A)) (Imp_f A A))"
    ).by_thm(CONJ(p.fact("k2"), p.fact("mp1")))
    p.thus("Prov_HF (Imp_f A A)").by(
        PROV_HF_MP, "Imp_f A (Imp_f A A)", "Imp_f A A", "k2_mp1"
    )


@proof
def PROV_HF_HYP_DROP(p):
    """|- !A B. is_form A /\\ is_form B /\\ Prov_HF B
                ==> Prov_HF (Imp_f A B).

    "Drop a hypothesis": from a HF-theorem ``B`` derive ``A -> B`` for
    any well-formed ``A``. One MP through K at (B, A): K gives
    ``B -> (A -> B)``; MP with ``Prov_HF B`` yields ``Prov_HF (A -> B)``.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B /\\ Prov_HF B ==> Prov_HF (Imp_f A B)",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.fix("A B")
    p.assume("(hA, hB, hPB): is_form A /\\ is_form B /\\ Prov_HF B")

    # K at (B, A): Prov_HF (Imp_f B (Imp_f A B)).
    p.have("hB_A: is_form B /\\ is_form A").by_thm(CONJ(p.fact("hB"), p.fact("hA")))
    p.have("k_BA: Prov_HF (Imp_f B (Imp_f A B))").by(PROV_HF_K, "B", "A", "hB_A")

    # MP(hPB, k_BA): Prov_HF (Imp_f A B).
    p.have("mp_in: Prov_HF B /\\ Prov_HF (Imp_f B (Imp_f A B))").by_thm(
        CONJ(p.fact("hPB"), p.fact("k_BA"))
    )
    p.thus("Prov_HF (Imp_f A B)").by(PROV_HF_MP, "B", "Imp_f A B", "mp_in")


@proof
def PROV_HF_TRANS_IMP(p):
    """|- !A B C. is_form A /\\ is_form B /\\ is_form C
                  /\\ Prov_HF (Imp_f A B) /\\ Prov_HF (Imp_f B C)
                  ==> Prov_HF (Imp_f A C).

    Transitivity of HF-implication. Standard route:
      1. HYP_DROP on Prov_HF (Imp_f B C) with hyp A:
            Prov_HF (Imp_f A (Imp_f B C)).
      2. S at (A, B, C):
            Prov_HF ((A -> (B -> C)) -> ((A -> B) -> (A -> C))).
      3. MP twice yields Prov_HF (Imp_f A C).
    """
    p.goal(
        "!A B C. is_form A /\\ is_form B /\\ is_form C "
        "/\\ Prov_HF (Imp_f A B) /\\ Prov_HF (Imp_f B C) "
        "==> Prov_HF (Imp_f A C)",
        types={"A": nat0_ty, "B": nat0_ty, "C": nat0_ty},
    )
    p.fix("A B C")
    p.assume(
        "(hA, hB, hC, hAB, hBC): "
        "is_form A /\\ is_form B /\\ is_form C "
        "/\\ Prov_HF (Imp_f A B) /\\ Prov_HF (Imp_f B C)"
    )

    # is_form (Imp_f B C) for HYP_DROP.
    is_form_imp_BC = SPECL([p._parse("B"), p._parse("C")], IS_FORM_AT_IMP)
    p.have("hBC_form: is_form (Imp_f B C)").by_eq_mp(
        SYM(is_form_imp_BC), CONJ(p.fact("hB"), p.fact("hC"))
    )

    # Step 1: HYP_DROP gives A -> (B -> C).
    p.have("hyp_in: is_form A /\\ is_form (Imp_f B C) /\\ Prov_HF (Imp_f B C)").by_thm(
        CONJ(p.fact("hA"), CONJ(p.fact("hBC_form"), p.fact("hBC")))
    )
    p.have("p1: Prov_HF (Imp_f A (Imp_f B C))").by(
        PROV_HF_HYP_DROP, "A", "Imp_f B C", "hyp_in"
    )

    # Step 2: S at (A, B, C).
    p.have("h_S_conj: is_form A /\\ is_form B /\\ is_form C").by_thm(
        CONJ(p.fact("hA"), CONJ(p.fact("hB"), p.fact("hC")))
    )
    p.have(
        "p2: Prov_HF (Imp_f (Imp_f A (Imp_f B C)) "
        "                  (Imp_f (Imp_f A B) (Imp_f A C)))"
    ).by(PROV_HF_S, "A", "B", "C", "h_S_conj")

    # Step 3a: MP(p1, p2): Prov_HF ((A -> B) -> (A -> C)).
    p.have(
        "mp_a: Prov_HF (Imp_f A (Imp_f B C)) /\\ "
        "      Prov_HF (Imp_f (Imp_f A (Imp_f B C)) "
        "                    (Imp_f (Imp_f A B) (Imp_f A C)))"
    ).by_thm(CONJ(p.fact("p1"), p.fact("p2")))
    p.have("p3: Prov_HF (Imp_f (Imp_f A B) (Imp_f A C))").by(
        PROV_HF_MP, "Imp_f A (Imp_f B C)", "Imp_f (Imp_f A B) (Imp_f A C)", "mp_a"
    )

    # Step 3b: MP(hAB, p3): Prov_HF (Imp_f A C).
    p.have(
        "mp_b: Prov_HF (Imp_f A B) /\\       Prov_HF (Imp_f (Imp_f A B) (Imp_f A C))"
    ).by_thm(CONJ(p.fact("hAB"), p.fact("p3")))
    p.thus("Prov_HF (Imp_f A C)").by(PROV_HF_MP, "Imp_f A B", "Imp_f A C", "mp_b")


# ---------------------------------------------------------------------------
# Stage 2C (b') -- deduction-theorem combinator.
#
# PROV_HF_DT_MP is the "MP through a hypothesis": from ``A -> X`` and
# ``A -> (X -> Y)`` derive ``A -> Y``. One application of S(A, X, Y)
# plus two MPs.
#
# Together with PROV_HF_HYP_DROP (DT_AXIOM: dropping a fact ``X`` to
# ``A -> X``) and PROV_HF_IMP_REFL (DT_HYP: ``A -> A``), this gives the
# three combinators needed to mechanically transform a Hilbert-style
# proof of ``B`` from hypothesis ``A`` into ``Prov_HF (Imp_f A B)``,
# without explicit deduction-theorem reflection.
#
# Consumers: PROV_HF_DOUBLE_NEG_ELIM (8-step DT proof), PROV_HF_CONTRAP,
# PROV_HF_AND_*, ...
# ---------------------------------------------------------------------------


@proof
def PROV_HF_DT_MP(p):
    """|- !A X Y. is_form A /\\ is_form X /\\ is_form Y
                  /\\ Prov_HF (Imp_f A X)
                  /\\ Prov_HF (Imp_f A (Imp_f X Y))
                  ==> Prov_HF (Imp_f A Y).

    Deduction-theorem MP combinator. From DT-prefixed forms of two
    Hilbert steps, produce the DT-prefixed form of their MP. One S(A,
    X, Y) instance plus two MPs.
    """
    p.goal(
        "!A X Y. is_form A /\\ is_form X /\\ is_form Y "
        "/\\ Prov_HF (Imp_f A X) "
        "/\\ Prov_HF (Imp_f A (Imp_f X Y)) "
        "==> Prov_HF (Imp_f A Y)",
        types={"A": nat0_ty, "X": nat0_ty, "Y": nat0_ty},
    )
    p.fix("A X Y")
    p.assume(
        "(hA, hX, hY, hAX, hAXY): "
        "is_form A /\\ is_form X /\\ is_form Y "
        "/\\ Prov_HF (Imp_f A X) "
        "/\\ Prov_HF (Imp_f A (Imp_f X Y))"
    )

    # S at (A, X, Y): (A -> (X -> Y)) -> ((A -> X) -> (A -> Y)).
    p.have("h_S_conj: is_form A /\\ is_form X /\\ is_form Y").by_thm(
        CONJ(p.fact("hA"), CONJ(p.fact("hX"), p.fact("hY")))
    )
    p.have(
        "s1: Prov_HF (Imp_f (Imp_f A (Imp_f X Y)) "
        "                  (Imp_f (Imp_f A X) (Imp_f A Y)))"
    ).by(PROV_HF_S, "A", "X", "Y", "h_S_conj")

    # MP(hAXY, s1): (A -> X) -> (A -> Y).
    p.have(
        "mp1_in: Prov_HF (Imp_f A (Imp_f X Y)) /\\ "
        "        Prov_HF (Imp_f (Imp_f A (Imp_f X Y)) "
        "                      (Imp_f (Imp_f A X) (Imp_f A Y)))"
    ).by_thm(CONJ(p.fact("hAXY"), p.fact("s1")))
    p.have("mp1: Prov_HF (Imp_f (Imp_f A X) (Imp_f A Y))").by(
        PROV_HF_MP,
        "Imp_f A (Imp_f X Y)",
        "Imp_f (Imp_f A X) (Imp_f A Y)",
        "mp1_in",
    )

    # MP(hAX, mp1): A -> Y.
    p.have(
        "mp2_in: Prov_HF (Imp_f A X) /\\ "
        "        Prov_HF (Imp_f (Imp_f A X) (Imp_f A Y))"
    ).by_thm(CONJ(p.fact("hAX"), p.fact("mp1")))
    p.thus("Prov_HF (Imp_f A Y)").by(
        PROV_HF_MP, "Imp_f A X", "Imp_f A Y", "mp2_in"
    )


@proof
def PROV_HF_EX_FALSO(p):
    """|- !A B. is_form A /\\ is_form B
                ==> Prov_HF (Imp_f (Not_f A) (Imp_f A B)).

    "Ex falso quodlibet" / Mendelson Lemma 1.10(a).
    Direct chain: ``K`` gives ``~A -> (~B -> ~A)``; ``N`` at (A, B)
    gives ``(~B -> ~A) -> (A -> B)``; TRANS_IMP composes them.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B ==> Prov_HF (Imp_f (Not_f A) (Imp_f A B))",
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
    p.have("hNBNA_form: is_form (Imp_f (Not_f B) (Not_f A))").by_eq_mp(
        SYM(is_form_imp_NB_NA), CONJ(p.fact("hNB"), p.fact("hNA"))
    )
    is_form_imp_AB = SPECL([p._parse("A"), p._parse("B")], IS_FORM_AT_IMP)
    p.have("hAB_form: is_form (Imp_f A B)").by_eq_mp(
        SYM(is_form_imp_AB), CONJ(p.fact("hA"), p.fact("hB"))
    )

    # K at (~A, ~B): ~A -> (~B -> ~A).
    p.have("h_K_in: is_form (Not_f A) /\\ is_form (Not_f B)").by_thm(
        CONJ(p.fact("hNA"), p.fact("hNB"))
    )
    p.have("k1: Prov_HF (Imp_f (Not_f A) (Imp_f (Not_f B) (Not_f A)))").by(
        PROV_HF_K, "Not_f A", "Not_f B", "h_K_in"
    )

    # N at (A, B): (~B -> ~A) -> (A -> B).
    p.have("n1: Prov_HF (Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B))").by(
        PROV_HF_N, "A", "B", CONJ(p.fact("hA"), p.fact("hB"))
    )

    # TRANS_IMP: ~A -> (~B -> ~A), (~B -> ~A) -> (A -> B), so ~A -> (A -> B).
    p.have(
        "h_T_conj: is_form (Not_f A) "
        "/\\ is_form (Imp_f (Not_f B) (Not_f A)) "
        "/\\ is_form (Imp_f A B) "
        "/\\ Prov_HF (Imp_f (Not_f A) (Imp_f (Not_f B) (Not_f A))) "
        "/\\ Prov_HF (Imp_f (Imp_f (Not_f B) (Not_f A)) (Imp_f A B))"
    ).by_thm(
        CONJ(
            p.fact("hNA"),
            CONJ(
                p.fact("hNBNA_form"),
                CONJ(p.fact("hAB_form"), CONJ(p.fact("k1"), p.fact("n1"))),
            ),
        )
    )
    p.thus("Prov_HF (Imp_f (Not_f A) (Imp_f A B))").by(
        PROV_HF_TRANS_IMP,
        "Not_f A",
        "Imp_f (Not_f B) (Not_f A)",
        "Imp_f A B",
        "h_T_conj",
    )


# ---------------------------------------------------------------------------
# Stage 2C (b'') -- DTChain builder.
#
# A Python-level utility for writing DT-transformed Hilbert proofs
# without is_form bookkeeping or CONJ-tree assembly. Wraps the three
# DT combinators (PROV_HF_IMP_REFL, PROV_HF_HYP_DROP, PROV_HF_DT_MP)
# behind a step-builder API; tracks is_form facts in a table keyed by
# kernel-term aconv-equality so callers don't have to re-prove
# is_form for repeated subterms.
#
# Usage pattern (for a Hilbert proof of ``B`` from hypothesis ``A``
# using only K/S/N axioms + MP):
#
#     dt = DTChain(p, "<A as string>", "<is_form A fact>")
#     dt.isf("X1", "<is_form X1 fact>")   # leaf is_form facts
#     dt.isf_not("X1")                     # auto-derive is_form (Not_f X1)
#     dt.isf_imp("X1", "X2")               # auto-derive is_form (Imp_f X1 X2)
#     # ...
#     # User derives Hilbert axiom instances independently:
#     p.have("hilb1: Prov_HF X").by(PROV_HF_K, ...)
#     # ...
#     # Then build the DT chain step-by-step:
#     s0 = dt.hyp()                        # A -> A
#     s1 = dt.axiom("X", "hilb1")          # A -> X (HYP_DROP)
#     s2 = dt.mp(s0, s1, "Y")              # A -> Y (DT_MP)
#     # ...
#     dt.discharge(s_final)                # p.thus(Imp_f A <step term>)
#
# A typical 8-step Hilbert proof becomes ~30 lines instead of ~250.
# ---------------------------------------------------------------------------


class DTChain:
    """Builder for DT-transformed Hilbert chains.

    Each step represents one Hilbert step prefixed with the chain's
    antecedent ``A``. The internal step list stores ``(kernel_term,
    fact_label)`` per step; the is_form table caches ``is_form X``
    facts keyed by kernel-term aconv-equality so the same subterm
    yields the same fact label across the proof.

    Methods are non-throwing on success; raise ``HolError`` on
    misuse (missing is_form, malformed term, etc.). Step indices are
    returned by builder methods and consumed by ``mp`` / ``discharge``.
    """

    def __init__(self, p, hyp_str: str, hyp_form_fact: str):
        """Begin a chain with antecedent ``hyp_str``.

        ``hyp_form_fact`` is the label of an existing fact in ``p``'s
        scope of shape ``is_form <hyp_str>``.
        """
        self.p = p
        self.hyp_str = hyp_str
        self.hyp_term = p._parse(hyp_str)
        self.hyp_form_fact = hyp_form_fact
        # is_form table: list of (kernel_term, fact_label).
        self._isf_table = [(self.hyp_term, hyp_form_fact)]
        # Step list: list of (body_kernel_term, dt_fact_label).
        self._steps = []
        self._counter = 0

    # ----- internal helpers -----

    def _fresh(self, prefix: str) -> str:
        self._counter += 1
        return f"_dtc{self._counter}_{prefix}"

    def _lookup_isf(self, term):
        for (t, lbl) in self._isf_table:
            if aconv(t, term):
                return lbl
        return None

    def _require_isf(self, term, term_str: str) -> str:
        lbl = self._lookup_isf(term)
        if lbl is None:
            raise ValueError(
                f"DTChain: no is_form fact registered for {term_str!r}; "
                f"call dt.isf({term_str!r}, ...) or one of dt.isf_not / "
                f"dt.isf_imp first."
            )
        return lbl

    # ----- is_form management -----

    def isf(self, term_str: str, fact_label: str) -> str:
        """Register an externally-proved is_form fact for ``term_str``.

        Idempotent: re-registering the same term (modulo aconv) returns
        the existing label without altering the table.
        """
        term = self.p._parse(term_str)
        existing = self._lookup_isf(term)
        if existing is not None:
            return existing
        self._isf_table.append((term, fact_label))
        return fact_label

    def get_isf(self, term_str: str) -> str:
        """Look up the registered is_form fact label for ``term_str``.

        Raises ``ValueError`` if no fact is registered (modulo aconv).
        """
        term = self.p._parse(term_str)
        return self._require_isf(term, term_str)

    def isf_not(self, base_str: str) -> str:
        """Auto-derive ``is_form (Not_f <base>)`` from ``is_form <base>``.

        Returns the new fact label; idempotent for the same base term.
        """
        base_term = self.p._parse(base_str)
        target_str = f"Not_f ({base_str})"
        target_term = self.p._parse(target_str)
        existing = self._lookup_isf(target_term)
        if existing is not None:
            return existing
        base_fact = self._require_isf(base_term, base_str)
        isf_at = SPEC(base_term, IS_FORM_AT_NOT)
        label = self._fresh("isfn")
        self.p.have(
            f"{label}: is_form (Not_f ({base_str}))"
        ).by_eq_mp(SYM(isf_at), base_fact)
        self._isf_table.append((target_term, label))
        return label

    def isf_imp(self, A_str: str, B_str: str) -> str:
        """Auto-derive ``is_form (Imp_f <A> <B>)`` from is_form A and is_form B.

        Returns the new fact label; idempotent for the same (A, B).
        """
        A_term = self.p._parse(A_str)
        B_term = self.p._parse(B_str)
        target_str = f"Imp_f ({A_str}) ({B_str})"
        target_term = self.p._parse(target_str)
        existing = self._lookup_isf(target_term)
        if existing is not None:
            return existing
        A_fact = self._require_isf(A_term, A_str)
        B_fact = self._require_isf(B_term, B_str)
        isf_at = SPECL([A_term, B_term], IS_FORM_AT_IMP)
        label = self._fresh("isfi")
        self.p.have(
            f"{label}: is_form (Imp_f ({A_str}) ({B_str}))"
        ).by_eq_mp(
            SYM(isf_at),
            CONJ(self.p.fact(A_fact), self.p.fact(B_fact)),
        )
        self._isf_table.append((target_term, label))
        return label

    # ----- step builders -----

    def hyp(self) -> int:
        """Step ``A -> A`` via PROV_HF_IMP_REFL. Returns the step index."""
        body_term = self.hyp_term
        label = self._fresh("dt_hyp")
        self.p.have(
            f"{label}: Prov_HF (Imp_f ({self.hyp_str}) ({self.hyp_str}))"
        ).by(PROV_HF_IMP_REFL, self.hyp_str, self.hyp_form_fact)
        idx = len(self._steps)
        self._steps.append((body_term, label))
        return idx

    def axiom(self, X_str: str, hilb_fact: str) -> int:
        """DT-wrap a closed axiom ``Prov_HF X`` (named ``hilb_fact``) into ``A -> X``.

        Caller must have:
          * a fact ``hilb_fact`` with conclusion ``Prov_HF <X>``;
          * ``is_form X`` registered with the chain (use ``isf``,
            ``isf_not``, or ``isf_imp``).
        """
        X_term = self.p._parse(X_str)
        X_form = self._require_isf(X_term, X_str)
        in_label = self._fresh("ax_in")
        self.p.have(
            f"{in_label}: is_form ({self.hyp_str}) "
            f"/\\ is_form ({X_str}) "
            f"/\\ Prov_HF ({X_str})"
        ).by_thm(
            CONJ(
                self.p.fact(self.hyp_form_fact),
                CONJ(self.p.fact(X_form), self.p.fact(hilb_fact)),
            )
        )
        out_label = self._fresh("dt_ax")
        self.p.have(
            f"{out_label}: Prov_HF (Imp_f ({self.hyp_str}) ({X_str}))"
        ).by(PROV_HF_HYP_DROP, self.hyp_str, X_str, in_label)
        idx = len(self._steps)
        self._steps.append((X_term, out_label))
        return idx

    def mp(self, i: int, j: int, Y_str: str) -> int:
        """Combine step i (``A -> X``) and step j (``A -> (X -> Y)``) into ``A -> Y``.

        ``Y_str`` is required because parsing the consequent out of step
        j's stored term-string is unreliable; supplying Y explicitly is
        unambiguous and matches how the user already thinks about the
        Hilbert step. ``is_form Y`` must already be registered.
        """
        if i < 0 or i >= len(self._steps):
            raise IndexError(f"DTChain.mp: step index {i} out of range")
        if j < 0 or j >= len(self._steps):
            raise IndexError(f"DTChain.mp: step index {j} out of range")
        X_term, dt_AX = self._steps[i]
        XtoY_term, dt_AXtoY = self._steps[j]
        Y_term = self.p._parse(Y_str)
        # Sanity: step j's body should be Imp_f X Y. Reconstruct and
        # check via aconv.
        expected_XtoY = mk_app(self.p._parse("Imp_f"), X_term)
        expected_XtoY = mk_app(expected_XtoY, Y_term)
        if not aconv(XtoY_term, expected_XtoY):
            raise ValueError(
                f"DTChain.mp: step {j}'s body does not match Imp_f "
                f"<step {i}> {Y_str!r}; check argument order."
            )
        # is_form for X (already known via step i's registration is not
        # automatic; require it explicitly).
        X_str_pp = self._term_to_str(X_term)
        X_form = self._require_isf(X_term, X_str_pp)
        Y_form = self._require_isf(Y_term, Y_str)
        in_label = self._fresh("mp_in")
        self.p.have(
            f"{in_label}: is_form ({self.hyp_str}) "
            f"/\\ is_form ({X_str_pp}) "
            f"/\\ is_form ({Y_str}) "
            f"/\\ Prov_HF (Imp_f ({self.hyp_str}) ({X_str_pp})) "
            f"/\\ Prov_HF (Imp_f ({self.hyp_str}) "
            f"                  (Imp_f ({X_str_pp}) ({Y_str})))"
        ).by_thm(
            CONJ(
                self.p.fact(self.hyp_form_fact),
                CONJ(
                    self.p.fact(X_form),
                    CONJ(
                        self.p.fact(Y_form),
                        CONJ(self.p.fact(dt_AX), self.p.fact(dt_AXtoY)),
                    ),
                ),
            )
        )
        out_label = self._fresh("dt_mp")
        self.p.have(
            f"{out_label}: Prov_HF (Imp_f ({self.hyp_str}) ({Y_str}))"
        ).by(PROV_HF_DT_MP, self.hyp_str, X_str_pp, Y_str, in_label)
        idx = len(self._steps)
        self._steps.append((Y_term, out_label))
        return idx

    def _term_to_str(self, term) -> str:
        """Pretty-print a kernel term to a parser-roundtrippable string.

        Used internally by ``mp`` and ``term`` to recover a string form
        for stored step bodies. ``parser.pp`` produces fully-parenthesised
        output that the parser accepts, so round-trip is safe even when
        the user's original input differed in spacing.
        """
        from parser import pp
        return pp(term)

    # ----- accessors / closure -----

    def fact(self, idx: int) -> str:
        """Return the fact label for step ``idx`` (i.e. the DT-prefixed Prov_HF).
        """
        return self._steps[idx][1]

    def term(self, idx: int) -> str:
        """Return step ``idx``'s body term as a pretty-printed string."""
        return self._term_to_str(self._steps[idx][0])

    def discharge(self, idx: int) -> None:
        """Discharge the active goal as ``Prov_HF (Imp_f A <step idx body>)``.

        Use when the goal is the implication form. The fact at step
        ``idx`` should have exactly the right shape; this is a
        ``p.thus(...).by_thm(p.fact(...))`` shortcut.
        """
        body_str = self.term(idx)
        self.p.thus(
            f"Prov_HF (Imp_f ({self.hyp_str}) ({body_str}))"
        ).by_thm(self.p.fact(self._steps[idx][1]))


# ---------------------------------------------------------------------------
# Stage 2C (c) -- negation reasoning.
#
# Headlines (Mendelson Lemma 1.11):
#   * ``A -> ~~A`` (double-negation introduction)
#   * ``~~A -> A`` (double-negation elimination)
#
# Both via the N axiom ``(~B -> ~A) -> (A -> B)`` plus K/S manipulation.
# Built using the DTChain helper to keep the visible structure 1-to-1
# with the Hilbert steps.
# ---------------------------------------------------------------------------


@proof
def PROV_HF_DOUBLE_NEG_ELIM_IMP(p):
    """|- !A. is_form A ==> Prov_HF (Imp_f (Not_f (Not_f A)) A).

    Mendelson Lemma 1.11(a) at the implication level. Owns the 8-step
    DT-transformed Hilbert derivation of ``~~A -> A``; the rule-form
    ``PROV_HF_DOUBLE_NEG_ELIM`` and the dual ``PROV_HF_DOUBLE_NEG_INTRO``
    both consume this lemma to avoid re-deriving the chain.

    Hilbert proof (under hypothesis ~~A):
      1. ~~A                          [hyp]
      2. ~~A -> (~~~~A -> ~~A)        [K(~~A, ~~~~A)]
      3. ~~~~A -> ~~A                  [MP 1, 2]
      4. (~~~~A -> ~~A) -> (~A -> ~~~A) [N(~A, ~~~A)]
      5. ~A -> ~~~A                    [MP 3, 4]
      6. (~A -> ~~~A) -> (~~A -> A)    [N(~~A, A)]
      7. ~~A -> A                      [MP 5, 6]
      8. A                             [MP 1, 7]

    DT transformation: each step gets ``~~A ->`` prefix; K/N-axiom
    steps wrap via PROV_HF_HYP_DROP, MP steps combine via
    PROV_HF_DT_MP. The final dt8 result is exactly the goal of this
    lemma, so no further MP is performed.
    """
    p.goal(
        "!A. is_form A ==> Prov_HF (Imp_f (Not_f (Not_f A)) A)",
        types={"A": nat0_ty},
    )
    p.fix("A")
    p.assume("hA: is_form A")

    # Pre-derive is_form (Not_f A) and is_form (Not_f (Not_f A)) so the
    # DTChain antecedent has its is_form fact in scope. Higher levels
    # are auto-derived via dt.isf_not.
    isf_A_at = SPEC(p._parse("A"), IS_FORM_AT_NOT)
    p.have("hnA: is_form (Not_f A)").by_eq_mp(SYM(isf_A_at), "hA")
    isf_nA_at = SPEC(p._parse("Not_f A"), IS_FORM_AT_NOT)
    p.have("hnnA: is_form (Not_f (Not_f A))").by_eq_mp(SYM(isf_nA_at), "hnA")

    # === DTChain setup. Antecedent is ~~A; auto-derive higher levels. ===
    dt = DTChain(p, "Not_f (Not_f A)", "hnnA")
    dt.isf("A", "hA")
    dt.isf("Not_f A", "hnA")
    dt.isf_not("Not_f (Not_f A)")          # is_form (Not_f^3 A)
    dt.isf_not("Not_f (Not_f (Not_f A))")  # is_form (Not_f^4 A)
    dt.isf_imp("Not_f (Not_f (Not_f (Not_f A)))", "Not_f (Not_f A)")  # K-body's RHS
    dt.isf_imp("Not_f A", "Not_f (Not_f (Not_f A))")                  # N4-body's RHS
    dt.isf_imp("Not_f (Not_f A)", "A")                                # N6-body's RHS
    # Full axiom-instance bodies (consumed by dt.axiom calls).
    dt.isf_imp(
        "Not_f (Not_f A)",
        "Imp_f (Not_f (Not_f (Not_f (Not_f A)))) (Not_f (Not_f A))",
    )  # K body: ~~A -> (~~~~A -> ~~A)
    dt.isf_imp(
        "Imp_f (Not_f (Not_f (Not_f (Not_f A)))) (Not_f (Not_f A))",
        "Imp_f (Not_f A) (Not_f (Not_f (Not_f A)))",
    )  # N4 body: (~~~~A -> ~~A) -> (~A -> ~~~A)
    dt.isf_imp(
        "Imp_f (Not_f A) (Not_f (Not_f (Not_f A)))",
        "Imp_f (Not_f (Not_f A)) A",
    )  # N6 body: (~A -> ~~~A) -> (~~A -> A)

    # === Hilbert axiom instances (closed Prov_HF X formulas). ===
    # Step 2: K(~~A, ~~~~A): Prov_HF (~~A -> (~~~~A -> ~~A)).
    p.have(
        "hilb2: Prov_HF (Imp_f (Not_f (Not_f A)) "
        "                     (Imp_f (Not_f (Not_f (Not_f (Not_f A)))) "
        "                            (Not_f (Not_f A))))"
    ).by(
        PROV_HF_K,
        "Not_f (Not_f A)",
        "Not_f (Not_f (Not_f (Not_f A)))",
        CONJ(p.fact("hnnA"), p.fact(dt.get_isf("Not_f (Not_f (Not_f (Not_f A)))"))),
    )
    # Step 4: N(~A, ~~~A): Prov_HF ((~~~~A -> ~~A) -> (~A -> ~~~A)).
    p.have(
        "hilb4: Prov_HF (Imp_f (Imp_f (Not_f (Not_f (Not_f (Not_f A)))) "
        "                            (Not_f (Not_f A))) "
        "                     (Imp_f (Not_f A) "
        "                            (Not_f (Not_f (Not_f A)))))"
    ).by(
        PROV_HF_N,
        "Not_f A",
        "Not_f (Not_f (Not_f A))",
        CONJ(p.fact("hnA"), p.fact(dt.get_isf("Not_f (Not_f (Not_f A))"))),
    )
    # Step 6: N(~~A, A): Prov_HF ((~A -> ~~~A) -> (~~A -> A)).
    p.have(
        "hilb6: Prov_HF (Imp_f (Imp_f (Not_f A) "
        "                            (Not_f (Not_f (Not_f A)))) "
        "                     (Imp_f (Not_f (Not_f A)) A))"
    ).by(
        PROV_HF_N,
        "Not_f (Not_f A)",
        "A",
        CONJ(p.fact("hnnA"), p.fact("hA")),
    )

    # === DT-prefixed Hilbert chain. Eight steps mirror the Hilbert proof. ===
    s1 = dt.hyp()
    s2 = dt.axiom(
        "Imp_f (Not_f (Not_f A)) "
        "      (Imp_f (Not_f (Not_f (Not_f (Not_f A)))) (Not_f (Not_f A)))",
        "hilb2",
    )
    s3 = dt.mp(
        s1, s2,
        "Imp_f (Not_f (Not_f (Not_f (Not_f A)))) (Not_f (Not_f A))",
    )
    s4 = dt.axiom(
        "Imp_f (Imp_f (Not_f (Not_f (Not_f (Not_f A)))) (Not_f (Not_f A))) "
        "      (Imp_f (Not_f A) (Not_f (Not_f (Not_f A))))",
        "hilb4",
    )
    s5 = dt.mp(s3, s4, "Imp_f (Not_f A) (Not_f (Not_f (Not_f A)))")
    s6 = dt.axiom(
        "Imp_f (Imp_f (Not_f A) (Not_f (Not_f (Not_f A)))) "
        "      (Imp_f (Not_f (Not_f A)) A)",
        "hilb6",
    )
    s7 = dt.mp(s5, s6, "Imp_f (Not_f (Not_f A)) A")
    s8 = dt.mp(s1, s7, "A")
    dt.discharge(s8)


@proof
def PROV_HF_DOUBLE_NEG_ELIM(p):
    """|- !A. is_form A /\\ Prov_HF (Not_f (Not_f A)) ==> Prov_HF A.

    Rule-form wrapper around PROV_HF_DOUBLE_NEG_ELIM_IMP plus one MP.
    """
    p.goal(
        "!A. is_form A /\\ Prov_HF (Not_f (Not_f A)) ==> Prov_HF A",
        types={"A": nat0_ty},
    )
    p.fix("A")
    p.assume("(hA, hPnnA): is_form A /\\ Prov_HF (Not_f (Not_f A))")

    p.have("h_imp: Prov_HF (Imp_f (Not_f (Not_f A)) A)").by(
        PROV_HF_DOUBLE_NEG_ELIM_IMP, "A", "hA"
    )
    p.have(
        "h_mp_in: Prov_HF (Not_f (Not_f A)) "
        "/\\ Prov_HF (Imp_f (Not_f (Not_f A)) A)"
    ).by_thm(CONJ(p.fact("hPnnA"), p.fact("h_imp")))
    p.thus("Prov_HF A").by(
        PROV_HF_MP, "Not_f (Not_f A)", "A", "h_mp_in"
    )


@proof
def PROV_HF_DOUBLE_NEG_INTRO(p):
    """|- !A. is_form A /\\ Prov_HF A ==> Prov_HF (Not_f (Not_f A)).

    Mendelson Lemma 1.11(b): double-negation introduction. Three steps:
      1. ``~~~A -> ~A``                 [ELIM_IMP at ~A]
      2. ``(~~~A -> ~A) -> (A -> ~~A)`` [N(A, ~~A)]
      3. ``A -> ~~A``                   [MP 1, 2]
    Then one final MP with the supplied ``Prov_HF A`` to close the rule
    form.
    """
    p.goal(
        "!A. is_form A /\\ Prov_HF A ==> Prov_HF (Not_f (Not_f A))",
        types={"A": nat0_ty},
    )
    p.fix("A")
    p.assume("(hA, hPA): is_form A /\\ Prov_HF A")

    # is_form for ~A and ~~A (needed by ELIM_IMP at ~A and N(A, ~~A)).
    isf_A = SPEC(p._parse("A"), IS_FORM_AT_NOT)
    p.have("hnA: is_form (Not_f A)").by_eq_mp(SYM(isf_A), "hA")
    isf_nA = SPEC(p._parse("Not_f A"), IS_FORM_AT_NOT)
    p.have("hnnA: is_form (Not_f (Not_f A))").by_eq_mp(SYM(isf_nA), "hnA")

    # Step 1: ELIM_IMP at ~A gives Prov_HF (~~~A -> ~A).
    p.have(
        "h1: Prov_HF (Imp_f (Not_f (Not_f (Not_f A))) (Not_f A))"
    ).by(PROV_HF_DOUBLE_NEG_ELIM_IMP, "Not_f A", "hnA")

    # Step 2: N(A, ~~A) gives (~~~A -> ~A) -> (A -> ~~A).
    p.have(
        "h2: Prov_HF (Imp_f "
        "  (Imp_f (Not_f (Not_f (Not_f A))) (Not_f A)) "
        "  (Imp_f A (Not_f (Not_f A))))"
    ).by(
        PROV_HF_N,
        "A",
        "Not_f (Not_f A)",
        CONJ(p.fact("hA"), p.fact("hnnA")),
    )

    # Step 3: MP h1 h2 gives Prov_HF (A -> ~~A).
    p.have(
        "h_mp1_in: Prov_HF (Imp_f (Not_f (Not_f (Not_f A))) (Not_f A)) "
        "/\\ Prov_HF (Imp_f "
        "    (Imp_f (Not_f (Not_f (Not_f A))) (Not_f A)) "
        "    (Imp_f A (Not_f (Not_f A))))"
    ).by_thm(CONJ(p.fact("h1"), p.fact("h2")))
    p.have(
        "h_imp: Prov_HF (Imp_f A (Not_f (Not_f A)))"
    ).by(
        PROV_HF_MP,
        "Imp_f (Not_f (Not_f (Not_f A))) (Not_f A)",
        "Imp_f A (Not_f (Not_f A))",
        "h_mp1_in",
    )

    # Final: MP h_imp with hPA.
    p.have(
        "h_final_in: Prov_HF A "
        "/\\ Prov_HF (Imp_f A (Not_f (Not_f A)))"
    ).by_thm(CONJ(p.fact("hPA"), p.fact("h_imp")))
    p.thus("Prov_HF (Not_f (Not_f A))").by(
        PROV_HF_MP, "A", "Not_f (Not_f A)", "h_final_in"
    )


# ---------------------------------------------------------------------------
# Stage 2C (d) -- conjunction and biconditional introduction.
#
# Encoded forms (since HF's primitives are Imp_f / Not_f only):
#   And_f A B  =  Not_f (Imp_f A (Not_f B))
#   Iff_f A B  =  Not_f (Imp_f (Imp_f A B) (Not_f (Imp_f B A)))
#                          (= And_f (Imp_f A B) (Imp_f B A))
# ---------------------------------------------------------------------------


@proof
def PROV_HF_AND_INTRO(p):
    """|- !A B. is_form A /\\ is_form B /\\ Prov_HF A /\\ Prov_HF B
                ==> Prov_HF (Not_f (Imp_f A (Not_f B))).

    Conjunction-introduction in HF. STUB; see implementation below.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B /\\ Prov_HF A /\\ Prov_HF B "
        "==> Prov_HF (Not_f (Imp_f A (Not_f B)))",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.sorry()


@proof
def PROV_HF_IFF_INTRO(p):
    """|- !A B. is_form A /\\ is_form B
                /\\ Prov_HF (Imp_f A B) /\\ Prov_HF (Imp_f B A)
                ==> Prov_HF (Not_f (Imp_f (Imp_f A B)
                                          (Not_f (Imp_f B A)))).

    Biconditional-introduction in HF. Direct application of AND_INTRO at
    the two implication directions: the conjunction of (A->B) and
    (B->A) is exactly the encoded biconditional.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B "
        "/\\ Prov_HF (Imp_f A B) /\\ Prov_HF (Imp_f B A) "
        "==> Prov_HF (Not_f (Imp_f (Imp_f A B) "
        "                         (Not_f (Imp_f B A))))",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.fix("A B")
    p.assume(
        "(hA, hB, hAB, hBA): "
        "is_form A /\\ is_form B "
        "/\\ Prov_HF (Imp_f A B) /\\ Prov_HF (Imp_f B A)"
    )

    # is_form (Imp_f A B), is_form (Imp_f B A) for AND_INTRO.
    is_form_imp_AB = SPECL([p._parse("A"), p._parse("B")], IS_FORM_AT_IMP)
    is_form_imp_BA = SPECL([p._parse("B"), p._parse("A")], IS_FORM_AT_IMP)
    p.have("hABf: is_form (Imp_f A B)").by_eq_mp(
        SYM(is_form_imp_AB), CONJ(p.fact("hA"), p.fact("hB"))
    )
    p.have("hBAf: is_form (Imp_f B A)").by_eq_mp(
        SYM(is_form_imp_BA), CONJ(p.fact("hB"), p.fact("hA"))
    )

    # AND_INTRO at (Imp_f A B, Imp_f B A) gives the encoded And_f form.
    p.have(
        "and_in: is_form (Imp_f A B) /\\ is_form (Imp_f B A) "
        "        /\\ Prov_HF (Imp_f A B) /\\ Prov_HF (Imp_f B A)"
    ).by_thm(
        CONJ(p.fact("hABf"), CONJ(p.fact("hBAf"), CONJ(p.fact("hAB"), p.fact("hBA"))))
    )
    p.thus("Prov_HF (Not_f (Imp_f (Imp_f A B) (Not_f (Imp_f B A))))").by(
        PROV_HF_AND_INTRO, "Imp_f A B", "Imp_f B A", "and_in"
    )


# ---------------------------------------------------------------------------
# Stage 2C (e) -- existential introduction.
#
# Exists_f x F = Not_f (Forall_f x (Not_f F)).
#
# Standard derivation: from a witness ``Prov_HF (substitute F t x)``,
# combine with the UI axiom (specialised at the negation) and N to
# derive ``Prov_HF (Not_f (Forall_f x (Not_f F)))``.
# ---------------------------------------------------------------------------


@proof
def PROV_HF_EXISTS_INTRO(p):
    """|- !x F t. is_form F /\\ is_term t /\\ Prov_HF (substitute F t x)
                  ==> Prov_HF (Not_f (Forall_f x (Not_f F))).

    Existential-introduction in HF (encoded form). STUB; see
    implementation below.
    """
    p.goal(
        "!x F t. is_form F /\\ is_term t /\\ "
        "Prov_HF (substitute F t x) "
        "==> Prov_HF (Not_f (Forall_f x (Not_f F)))",
        types={"x": nat0_ty, "F": nat0_ty, "t": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2C (f) -- conjunction elimination (And_f projections).
#
# And_f A B = Not_f (Imp_f A (Not_f B)). Given the encoded form, the
# standard projections are:
#   ELIM_LEFT  : Prov_HF (~(A -> ~B)) ==> Prov_HF A
#   ELIM_RIGHT : Prov_HF (~(A -> ~B)) ==> Prov_HF B
#
# Each goes through DOUBLE_NEG_ELIM + N + S manipulation.
# ---------------------------------------------------------------------------


@proof
def PROV_HF_AND_ELIM_LEFT(p):
    """|- !A B. is_form A /\\ is_form B
                /\\ Prov_HF (Not_f (Imp_f A (Not_f B)))
                ==> Prov_HF A.

    Left projection of conjunction. STUB.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B "
        "/\\ Prov_HF (Not_f (Imp_f A (Not_f B))) "
        "==> Prov_HF A",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.sorry()


@proof
def PROV_HF_AND_ELIM_RIGHT(p):
    """|- !A B. is_form A /\\ is_form B
                /\\ Prov_HF (Not_f (Imp_f A (Not_f B)))
                ==> Prov_HF B.

    Right projection of conjunction. STUB.
    """
    p.goal(
        "!A B. is_form A /\\ is_form B "
        "/\\ Prov_HF (Not_f (Imp_f A (Not_f B))) "
        "==> Prov_HF B",
        types={"A": nat0_ty, "B": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2C (g) -- existential elimination (∃-elim).
#
# Hilbert formulation as a derivable rule:
#   If ``Prov_HF (Imp_f P Q)`` and ``v`` is not free in ``Q``,
#   then ``Prov_HF (Imp_f (Exists_f v P) Q)``.
#
# Encoded form (Exists_f v P = Not_f (Forall_f v (Not_f P))):
#   Prov_HF (Imp_f (Not_f (Forall_f v (Not_f P))) Q).
#
# Standard derivation: contrapositive via N axiom + Gen + Vac.
# ---------------------------------------------------------------------------


@proof
def PROV_HF_EXISTS_ELIM(p):
    """|- !v P Q. is_form P /\\ is_form Q /\\ ~(free_in Q v)
                  /\\ Prov_HF (Imp_f P Q)
                  ==> Prov_HF (Imp_f (Not_f (Forall_f v (Not_f P))) Q).

    Existential-elimination as a derived rule (encoded form). STUB.
    """
    p.goal(
        "!v P Q. is_form P /\\ is_form Q /\\ ~(free_in Q v) "
        "/\\ Prov_HF (Imp_f P Q) "
        "==> Prov_HF (Imp_f (Not_f (Forall_f v (Not_f P))) Q)",
        types={"v": nat0_ty, "P": nat0_ty, "Q": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2C (h) -- substitution under equality (Subst axiom in MP form).
#
# The is_Subst axiom schema, lifted through the disjunction chain to
# Prov_HF (slot 6 of is_logical_axiom). Direct analogue of PROV_HF_K /
# PROV_HF_S / PROV_HF_N -- could be filled in immediately by the same
# pattern (kept as a stub here only because the body's witness building
# is the same boilerplate).
# ---------------------------------------------------------------------------


@proof
def PROV_HF_SUBST_EQ(p):
    """|- !x F t1 t2. is_form F /\\ is_term t1 /\\ is_term t2
                      ==> Prov_HF (Imp_f (Eq_f t1 t2)
                                        (Imp_f (substitute F t1 x)
                                               (substitute F t2 x))).

    The is_Subst axiom in MP-friendly form. STUB; analogous to
    PROV_HF_K / PROV_HF_S / PROV_HF_N -- direct application of
    ``_prov_of_logical`` at slot 6.
    """
    p.goal(
        "!x F t1 t2. is_form F /\\ is_term t1 /\\ is_term t2 "
        "==> Prov_HF (Imp_f (Eq_f t1 t2) "
        "                  (Imp_f (substitute F t1 x) "
        "                         (substitute F t2 x)))",
        types={"x": nat0_ty, "F": nat0_ty, "t1": nat0_ty, "t2": nat0_ty},
    )
    p.sorry()


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 2C (a) -- axiom-instance specializations.")
    print("    PROV_HF_K :", pp_thm(PROV_HF_K))
    print("    PROV_HF_S :", pp_thm(PROV_HF_S))
    print("    PROV_HF_N :", pp_thm(PROV_HF_N))
    print()
    print("Stage 2C (a') -- universal instantiation.")
    print("    PROV_HF_UI :", pp_thm(PROV_HF_UI))
    print()
    print("Stage 2C (b) -- basic propositional reasoning.")
    print("    PROV_HF_IMP_REFL  :", pp_thm(PROV_HF_IMP_REFL))
    print("    PROV_HF_HYP_DROP  :", pp_thm(PROV_HF_HYP_DROP))
    print("    PROV_HF_TRANS_IMP :", pp_thm(PROV_HF_TRANS_IMP))
    print("    PROV_HF_EX_FALSO  :", pp_thm(PROV_HF_EX_FALSO))
    print()
    print("Stage 2C (c) -- negation reasoning.")
    print("    PROV_HF_DOUBLE_NEG_ELIM_IMP :", pp_thm(PROV_HF_DOUBLE_NEG_ELIM_IMP))
    print("    PROV_HF_DOUBLE_NEG_ELIM     :", pp_thm(PROV_HF_DOUBLE_NEG_ELIM))
    print("    PROV_HF_DOUBLE_NEG_INTRO    :", pp_thm(PROV_HF_DOUBLE_NEG_INTRO))
    print()
    print("Stage 2C (d) -- conjunction / biconditional intro (STUB).")
    print("    PROV_HF_AND_INTRO :", pp_thm(PROV_HF_AND_INTRO))
    print("    PROV_HF_IFF_INTRO :", pp_thm(PROV_HF_IFF_INTRO))
    print()
    print("Stage 2C (e) -- existential intro (STUB).")
    print("    PROV_HF_EXISTS_INTRO :", pp_thm(PROV_HF_EXISTS_INTRO))
    print()
    print("Stage 2C (f) -- conjunction elimination (STUB).")
    print("    PROV_HF_AND_ELIM_LEFT  :", pp_thm(PROV_HF_AND_ELIM_LEFT))
    print("    PROV_HF_AND_ELIM_RIGHT :", pp_thm(PROV_HF_AND_ELIM_RIGHT))
    print()
    print("Stage 2C (g) -- existential elimination (STUB).")
    print("    PROV_HF_EXISTS_ELIM :", pp_thm(PROV_HF_EXISTS_ELIM))
    print()
    print("Stage 2C (h) -- substitution under equality (STUB).")
    print("    PROV_HF_SUBST_EQ :", pp_thm(PROV_HF_SUBST_EQ))

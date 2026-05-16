"""Rice's theorem for SK combinators, parametric over a semantic property.

Final theorem (``RICE_THEOREM``):

    |- !P. par_conv_invariant P ==> ~ ?D. rice_decider P D

where, for ``P : nat0 -> bool``,

    par_conv_invariant P
        := !X Y. par_conv X Y ==> P X = P Y

    rice_decider P D
        := is_sk_term D /\\
           !t. is_sk_term t ==>
               (P t = ~(P (App_t D t)))

Reading: no SK term D decides any par_conv-invariant property P via the
flipped halt-status convention inherited from ``halting.py``.

------------------------------------------------------------------
Relation to the classical Rice statement
------------------------------------------------------------------

Classical Rice: for any nontrivial extensional property P of programs,
no program decides P (returning Church-true/false).  Two semantic
hypotheses normally appear -- extensionality and non-triviality -- but
under the flipped decider spec used here, non-triviality drops out
automatically: if P is constant, ``P t = ~(P (App_t D t))`` becomes
``T = F`` (or ``F = T``), refuting any candidate ``D``.  Only
``par_conv_invariant P`` survives as the genuine semantic input.

This file is the natural generalisation of ``HALTING_UNDECIDABLE`` in
``halting.py``: setting ``P := halts`` recovers halting, with
``par_conv_invariant halts`` discharged by ``HALTS_INVARIANT``.

------------------------------------------------------------------
Proof sketch (RICE_THEOREM)
------------------------------------------------------------------

The proof is mechanically the same as ``HALTING_UNDECIDABLE`` with P
abstracted:

  Assume D with ``rice_decider P D``.  Unfold:
    is_sk_term D /\\ !t. is_sk_term t ==>
                         P t = ~(P (App_t D t)).

  Parametric diagonal (``RICE_DIAGONAL``) at D:
    ?d. is_sk_term d /\\ P d = P (App_t D d).

  Specialise the decider spec at t := d:
    P d = ~(P (App_t D d)).

  Combining: P (App_t D d) = ~(P (App_t D d)).
  Discharge via EXCLUDED_MIDDLE on P (App_t D d).

The only ingredient that needs ``par_conv_invariant P`` is
``RICE_DIAGONAL``: ``DIAG_TERM`` already produces ``par_conv d
(App_t H d)``; invariance lifts that to ``P d = P (App_t H d)``.

------------------------------------------------------------------
Stage map
------------------------------------------------------------------

  Stage 0:  ``par_conv_invariant`` definition + unfold theorem.
  Stage 1:  ``rice_decider`` definition + unfold theorem.
  Stage 2:  ``RICE_DIAGONAL`` -- parametric diagonal lifted through P.
  Stage 3:  ``RICE_THEOREM`` -- headline.
  Stage 4:  ``RICE_NOT_SK_REPRESENTABLE`` -- unfolded restatement.
"""

from fusion import Var
from basics import mk_const, rand
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof
from tactics import SYM, TRANS

from halting import DIAG_TERM


# ---------------------------------------------------------------------------
# Stage 0 -- par_conv-invariance predicate on properties of SK terms.
#
#   par_conv_invariant P  iff  !X Y. par_conv X Y ==> P X = P Y.
#
# This is the semantic hypothesis under which Rice's theorem holds:
# P must respect par-convertibility (= extensionality wrt SK reduction).
# ---------------------------------------------------------------------------

_pred_ty = parse_type("nat0 -> bool")


PAR_CONV_INVARIANT_DEF = define(
    "par_conv_invariant",
    parse_type("(nat0 -> bool) -> bool"),
    "\\P:nat0->bool. !X:nat0. !Y:nat0. par_conv X Y ==> P X = P Y",
)
par_conv_invariant = mk_const("par_conv_invariant", [])


@proof
def PAR_CONV_INVARIANT_AT(p):
    """|- !P. par_conv_invariant P =
              (!X Y. par_conv X Y ==> P X = P Y).

    Direct unfold of PAR_CONV_INVARIANT_DEF via AP_THM + BETA, mirror
    of HALTS_AT / HALTS_DECIDER_DEF_THM in ``halting.py``.
    """
    p.goal(
        "!P:nat0->bool. par_conv_invariant P = "
        "    (!X:nat0. !Y:nat0. par_conv X Y ==> P X = P Y)"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 1 -- the flipped Rice-decider predicate, parametric in P.
#
#   rice_decider P D  iff  is_sk_term D /\\
#                          !t. is_sk_term t ==>
#                              (P t = ~(P (App_t D t))).
#
# Specialising P := halts recovers ``halts_decider`` from ``halting.py``.
# ---------------------------------------------------------------------------


RICE_DECIDER_DEF = define(
    "rice_decider",
    parse_type("(nat0 -> bool) -> nat0 -> bool"),
    "\\P:nat0->bool. \\D:nat0. "
    "    is_sk_term D /\\ "
    "    !t:nat0. is_sk_term t ==> "
    "        (P t = ~(P (App_t D t)))",
)
rice_decider = mk_const("rice_decider", [])


@proof
def RICE_DECIDER_DEF_THM(p):
    """|- !P D. rice_decider P D =
                (is_sk_term D /\\
                 !t. is_sk_term t ==>
                     (P t = ~(P (App_t D t)))).

    Direct unfold of RICE_DECIDER_DEF via two AP_THMs + BETA, mirror
    of ``HALTS_DECIDER_DEF_THM`` in ``halting.py``.
    """
    p.goal(
        "!P:nat0->bool. !D:nat0. rice_decider P D = "
        "    (is_sk_term D /\\ "
        "     !t:nat0. is_sk_term t ==> "
        "         (P t = ~(P (App_t D t))))"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2 -- parametric diagonal.
#
# For every SK term H, ``DIAG_TERM`` provides an SK term d with
#   par_conv d (App_t H d).
# If P is par_conv-invariant, this lifts to
#   P d = P (App_t H d).
# This is the only place ``par_conv_invariant P`` is consumed.
# ---------------------------------------------------------------------------


@proof
def RICE_DIAGONAL(p):
    """|- !P. par_conv_invariant P ==>
              !H. is_sk_term H ==>
                  ?d. is_sk_term d /\\ P d = P (App_t H d).

    Generalises ``DIAGONAL_TERM_EXISTS`` from ``halting.py`` (which is
    the special case P := halts).

    Proof:
      Fix P, assume ``par_conv_invariant P`` and unfold via
      PAR_CONV_INVARIANT_AT to obtain
        h_ext: !X Y. par_conv X Y ==> P X = P Y.
      Fix H, assume is_sk_term H.
      DIAG_TERM at H gives d with is_sk_term d /\\ par_conv d (App_t H d).
      Specialise h_ext at d, App_t H d to obtain P d = P (App_t H d).
      Witness d.
    """
    p.goal(
        "!P:nat0->bool. par_conv_invariant P ==> "
        "    !H:nat0. is_sk_term H ==> "
        "        ?d:nat0. is_sk_term d /\\ P d = P (App_t H d)"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 3 -- the headline theorem.
# ---------------------------------------------------------------------------


@proof
def RICE_THEOREM(p):
    """|- !P. par_conv_invariant P ==> ~ ?D. rice_decider P D.

    THE THEOREM.  No SK combinator decides any par_conv-invariant
    property P via the flipped halt-status convention.

    Proof (mirrors ``HALTING_UNDECIDABLE`` with P abstracted):

      Fix P, assume ``par_conv_invariant P``.
      Suppose ``?D. rice_decider P D``; choose D.
      Unfold via RICE_DECIDER_DEF_THM:
        is_sk_term D /\\ !t. is_sk_term t ==>
                             P t = ~(P (App_t D t)).

      RICE_DIAGONAL at P, D:
        ?d. is_sk_term d /\\ P d = P (App_t D d).
      Choose d.

      Specialise the decider spec at t := d:
        P d = ~(P (App_t D d)).

      Combining (SYM on the diagonal eq + TRANS):
        P (App_t D d) = ~(P (App_t D d)).

      Discharge via EXCLUDED_MIDDLE on P (App_t D d).
    """
    p.goal(
        "!P:nat0->bool. par_conv_invariant P ==> "
        "    ~ (?D:nat0. rice_decider P D)"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 4 -- corollary: unfolded restatement.
# ---------------------------------------------------------------------------


@proof
def RICE_NOT_SK_REPRESENTABLE(p):
    """|- !P. par_conv_invariant P ==>
              ~ ?D. is_sk_term D /\\
                    !t. is_sk_term t ==>
                        (P t = ~(P (App_t D t))).

    RICE_THEOREM, restated as non-existence of an SK term satisfying
    the unfolded flipped decider spec.  Mirror of
    ``HALTS_NOT_SK_REPRESENTABLE`` in ``halting.py``: any D satisfying
    the unfolded predicate also satisfies ``rice_decider P D`` (via
    RICE_DECIDER_DEF_THM), witnessing the existential refuted by
    RICE_THEOREM.
    """
    p.goal(
        "!P:nat0->bool. par_conv_invariant P ==> "
        "    ~ (?D:nat0. is_sk_term D /\\ "
        "               !t:nat0. is_sk_term t ==> "
        "                   (P t = ~(P (App_t D t))))"
    )
    p.sorry()


if __name__ == "__main__":
    from parser import pp_thm
    print("PAR_CONV_INVARIANT_DEF    :", pp_thm(PAR_CONV_INVARIANT_DEF))
    print("RICE_DECIDER_DEF          :", pp_thm(RICE_DECIDER_DEF))
    print("RICE_DIAGONAL             :", pp_thm(RICE_DIAGONAL))
    print("RICE_THEOREM              :", pp_thm(RICE_THEOREM))
    print("RICE_NOT_SK_REPRESENTABLE :", pp_thm(RICE_NOT_SK_REPRESENTABLE))

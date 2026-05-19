"""Demo / smoke test for fusion_dhol + basics_dhol.

Lives in its own file (rather than fusion_dhol.py's `if __name__ ==
"__main__":` block) so that the dataclasses (Pi, Var, Tyapp, ...) are
the same Python class objects whether referenced via fusion_dhol or via
basics_dhol's imports. Running fusion_dhol.py as __main__ used to
duplicate these classes, breaking isinstance() checks across module
boundaries."""

from fusion_dhol import (
    Tyvar, Tyapp, Pi, Subtype, Var, Const, Comb, Abs, Assume,
    bool_ty, aty,
    HolError,
    VAR, CONST, LAMBDA, CONV,
    REFL, ASSUME, BETA, EQ_TY_CONV, EQ_MP,
    DEDUCT_ANTISYM_RULE, INST, INST_TYPE,
    TY_REFL, TY_SYM, TY_TRANS, TY_CONG_BASE,
    THM_CONG_BASE,
    RESTRICT, RESTRICT_PROOF, FORGET_TYPING,
    CONCL_TYPING,
    mk_type, safe_mk_eq,
    new_type, new_constant, new_axiom, new_basic_definition,
    interpret, frees,
    _pp_ty, _pp_tm, _eq_tag, _tm_alpha,
)

# ETA, TRANS, UNRESTRICT, DISCH, MP, mk_imp now live in basics_dhol.
# APP, MK_COMB are imported from basics_dhol so the propositional domain
# bridge (`eq`) is available; ABS, TM_CONG_BASE, TY_PI, IMP_TYPE are
# kernel rules re-exported through basics_dhol. mk_arrow / mk_subtype /
# instantiate are non-kernel sugar living in basics_dhol.
from basics_dhol import (
    APP, MK_COMB, ABS, TM_CONG_BASE, TY_PI,
    ETA, TRANS, UNRESTRICT, DISCH, MP, IMP_TYPE, mk_imp,
    mk_arrow, mk_subtype, instantiate,
)

# nat as a base type, with 0 / S / add as inhabitants.
nat_ty = Tyapp("nat", (), ())
new_type("nat", phi=())
new_constant("0", nat_ty)
new_constant("S", mk_arrow(nat_ty, nat_ty))
new_constant("add", mk_arrow(nat_ty, mk_arrow(nat_ty, nat_ty)))

zero_th = CONST("0")
succ_th = CONST("S")
add_th = CONST("add")
one_th = APP(succ_th, zero_th)
two_th = APP(succ_th, one_th)
print("0   ::", _pp_ty(zero_th._ty))
print("S 0 ::", _pp_ty(one_th._ty))
print()

# vec : (n:nat) -> tp, with nil : vec(0) as a separately-declared inhabitant.
zero_const = Const("0", nat_ty)
nil_ty = Tyapp("vec", (), (zero_const,))
new_type("vec", phi=(Var("n", nat_ty),))
new_constant("nil", nil_ty)

def vec(n_th):
    return mk_type("vec", [n_th])

nil_th = CONST("nil")
print("nil ::", _pp_ty(nil_th._ty))

# cons : Pi(n:nat). nat -> vec n -> vec (S n)
n_var = Var("n", nat_ty)
n_th = VAR(n_var)
vec_n = vec(n_th)
vec_Sn = vec(APP(succ_th, n_th))
cons_ty = Pi(n_var, mk_arrow(nat_ty, mk_arrow(vec_n, vec_Sn)))
new_constant("cons", cons_ty)
cons_th = CONST("cons")

# Build cons 0 0 nil  ::  vec (S 0)
v1_th = APP(APP(APP(cons_th, zero_th), zero_th), nil_th)
print("cons 0 0 nil           ::", _pp_ty(v1_th._ty))

# Build cons 1 0 (cons 0 0 nil)  ::  vec (S (S 0))
v2_th = APP(APP(APP(cons_th, one_th), zero_th), v1_th)
print("cons 1 0 (cons 0 0 nil)::", _pp_ty(v2_th._ty))

# Definitional mismatch: cons 1 0 nil rejected (expects vec 1, got vec 0)
try:
    APP(APP(APP(cons_th, one_th), zero_th), nil_th)
except HolError as e:
    print("\nexpected failure:", str(e).splitlines()[0])

# ----------------------------------------------------------------
# Propositional type bridge.
#
# Axiom: forall n. add 0 n = n  -- we encode just the free-variable form
# |- add 0 n = n   (n a free variable of type nat).
# Then specialize to n := 0, lift to vec(add 0 0) == vec 0 via TY_CONG_BASE,
# and use the bridge to apply a function expecting vec 0 to a value
# whose type is vec(add 0 0).
# ----------------------------------------------------------------

print()
add_0_n = APP(APP(add_th, zero_th), VAR(n_var))
eq_form = APP(APP(CONST("=", (nat_ty,)), add_0_n), VAR(n_var))
print("axiom term ::", _pp_tm(eq_form._tm), ":", _pp_ty(eq_form._ty))
add_zero = new_axiom(eq_form, phi=(n_var,))  # (n:nat) ▷ add 0 n = n
print("axiom      ::", add_zero)

# Specialize n := 0 in one step via interpret(σ).
add_0_0_eq_0 = interpret(add_zero, (zero_th,))
print("interpreted::", add_0_0_eq_0)

# Lift to type equality vec(add 0 0) == vec 0
vec_bridge = TY_CONG_BASE("vec", [add_0_0_eq_0])
print("type bridge::", vec_bridge)

# Build a value of type vec(add 0 0) by CONV-ing nil : vec 0
nil_at_add = CONV(nil_th, TY_SYM(vec_bridge))
print("nil viewed as vec(add 0 0) ::", _pp_ty(nil_at_add._ty))

# Define a consumer  g : vec 0 -> nat
g_v = Var("v", vec(zero_th))
g_th = LAMBDA(g_v, zero_th)  # \v:vec(0). 0
print("g          ::", _pp_ty(g_th._ty))

# Now apply g to nil_at_add (whose type is vec(add 0 0), not vec 0).
# Without a bridge, APP rejects:
try:
    APP(g_th, nil_at_add)
except HolError as e:
    print("without bridge:", str(e).splitlines()[0])

# With the bridge, APP succeeds and the resulting typing absorbs the
# bridge's hypotheses (here empty, since the axiom was unconditional).
g_nil = APP(g_th, nil_at_add, eq=vec_bridge)
print("with bridge: g (nil :vec(add 0 0)) ::", _pp_ty(g_nil._ty))
print("             asl =", g_nil._asl)

# Wrap it into a regular theorem.
g_nil_refl = REFL(g_nil)
print("REFL(g nil) ::", g_nil_refl)

# ----------------------------------------------------------------
# INST also propagates the substitution into type annotations.
# Build |- cons n x v = cons n x v with v : vec n free, then INST
# n := zero. The free v should reappear as v : vec 0 in the result.
# ----------------------------------------------------------------
print()
x_var = Var("x", nat_ty)
v_var = Var("v", vec(n_th))  # v : vec n
cons_nxv_th = APP(APP(APP(cons_th, n_th), VAR(x_var)), VAR(v_var))
print("cons n x v ::", _pp_ty(cons_nxv_th._ty))
refl_cons = REFL(cons_nxv_th)
print("REFL       ::", refl_cons)
refl_cons_at_0 = INST([(zero_th, n_var)], refl_cons)
print("INST n:=0  ::", refl_cons_at_0)
# Inspect the Var occurrences in the new conclusion to confirm v's
# type annotation was rewritten from vec(n) to vec(0).
for free in frees(refl_cons_at_0._concl):
    print(f"  free var {free.name} :: {_pp_ty(free.ty)}")

# ----------------------------------------------------------------
# Sequential semantics: INST [(zero, n), (v_th, v)] where v_th has
# type vec(0) — matching v's declared type vec(n) only AFTER the
# earlier substitution n := 0 has been applied.
# ----------------------------------------------------------------
print()
nil_th_again = CONST("nil")  # vec(0)
seq_inst = INST([(zero_th, n_var), (nil_th_again, v_var)], refl_cons)
print("seq INST [n:=0, v:=nil] ::", seq_inst)

# ----------------------------------------------------------------
# Propositional bridging via CONV-then-INST. We have nil : vec(0)
# and want to substitute it for v : vec(n) with n eventually becoming
# `add 0 0`. The replacement's type after the n:=add 0 0 step would
# be vec(add 0 0), so we CONV nil from vec(0) to vec(add 0 0) using
# the bridge derived earlier, then INST sequentially.
# ----------------------------------------------------------------
print()
add00_th = APP(APP(add_th, zero_th), zero_th)        # add 0 0 : nat
nil_at_add00 = CONV(nil_th, vec_bridge)              # nil : vec(add 0 0)
print("nil : vec(0)  ==CONV==>  vec(add 0 0)  ::", _pp_ty(nil_at_add00._ty))
bridged_inst = INST(
    [(add00_th, n_var), (nil_at_add00, v_var)],
    refl_cons,
)
print("INST [n:=add 0 0, v:=nil (coerced)] ::", bridged_inst)
for free in frees(bridged_inst._concl):
    print(f"  free var {free.name} :: {_pp_ty(free.ty)}")

# ----------------------------------------------------------------
# ETA: eta-expand a Pi-typed term.
# ----------------------------------------------------------------
print()
succ_eta = ETA(succ_th)
print("ETA(S) ::", succ_eta)

# Eta-expanding cons applied to 0 (type nat -> vec 0 -> vec (S 0)).
cons0_eta = ETA(APP(cons_th, zero_th))
print("ETA(cons 0) ::", cons0_eta)

# Eta-expanding cons itself (dependent Pi: Pi(n:nat). ...). The basics_dhol
# ETA only covers non-dependent Pi (since ETA_AX is axiomatised at A->B);
# fully dependent eta needs rank-1 type ops, item 19 in dhol_missing.md.
try:
    cons_eta = ETA(cons_th)
    print("ETA(cons)   ::", cons_eta)
except HolError as e:
    print("ETA(cons)   :: rejected --", str(e).splitlines()[0])

# ----------------------------------------------------------------
# EQ_TY_CONV: re-tag an equation at a propositionally-equal type.
# ----------------------------------------------------------------
print()
def _eq_tag_str(th):
    return _pp_ty(_eq_tag(th._concl))

nil_refl = REFL(nil_th)
print(f"REFL(nil)                :: {nil_refl}  [= tagged at {_eq_tag_str(nil_refl)}]")
# The CONV'd typing_thm (nil_at_add : vec(add 0 0)) now flows its
# certificate type into REFL, so the equation gets tagged at
# vec(add 0 0), not at the intrinsic vec(0). Pre-fix this would
# have read type_of(nil) = vec(0).
nil_refl_via_cert = REFL(nil_at_add)
print(f"REFL(nil_at_add)         :: {nil_refl_via_cert}  "
      f"[= tagged at {_eq_tag_str(nil_refl_via_cert)}]")
# nil_refl's = constant is tagged at vec(0). Re-tag via the bridge
# vec(add 0 0) == vec(0) (which here happens to have empty asl).
nil_refl_at_add = EQ_TY_CONV(nil_refl, vec_bridge)
print(f"EQ_TY_CONV via vec_bridge:: {nil_refl_at_add}  [= tagged at {_eq_tag_str(nil_refl_at_add)}]")

# Demonstrate hypothesis propagation: ASSUME the same equation
# add 0 0 = 0, lift it, and use the resulting bridge in EQ_TY_CONV;
# the assumption should appear in the result's asl.
print()
assumed_eq = ASSUME(eq_form)  # not quite -- eq_form is the universally
                              # quantified form. Let's specialise:
# Build an assumption form with n bound to 0:
n0_eq = APP(APP(CONST("=", (nat_ty,)),
                APP(APP(add_th, zero_th), zero_th)),
            zero_th)
print("assumption term ::", _pp_tm(n0_eq._tm))
assumed_n0 = ASSUME(n0_eq)
print("ASSUME           ::", assumed_n0)
vec_bridge_hyp = TY_CONG_BASE("vec", [assumed_n0])
print("derived bridge   ::", vec_bridge_hyp)
nil_refl_hyp = EQ_TY_CONV(nil_refl, vec_bridge_hyp)
print(f"EQ_TY_CONV w/ hyp:: {nil_refl_hyp}  [= tagged at {_eq_tag_str(nil_refl_hyp)}]")

# ----------------------------------------------------------------
# new_type with no inhabitant: empty types are allowed (Rabe 2026
# §2). A theory that wants the type non-empty registers an
# inhabitant via a separate new_constant call.
# ----------------------------------------------------------------
print()
new_type("phantom", ())
print("declared phantom (no inhabitant)")
new_constant("ghost", Tyapp("phantom", (), ()))
print("registered inhabitant ghost : phantom")

# Re-declaration of an existing name is still rejected:
try:
    new_type("phantom", ())
except HolError as e:
    print("rejects re-declaration ::", str(e).splitlines()[0])

# ----------------------------------------------------------------
# congLambda' (ABS with binder-type bridge) and congAppl'
# (MK_COMB with codomain bridge): exercise the heterogeneous case.
# ----------------------------------------------------------------
print()
# Build (\v:vec 0. 0) = (\v:vec(add 0 0). 0) via ABS + the type
# bridge vec(0) == vec(add 0 0). REFL gives the body equality; the
# bridge is precisely vec_bridge (or its TY_SYM).
body_zero = REFL(zero_th)  # |- 0 = 0  at type nat
v_at_vec0 = Var("v", vec(zero_th))
abs_hetero = ABS(v_at_vec0, body_zero, ty_eq=TY_SYM(vec_bridge))
print("ABS with ty_eq ::", abs_hetero)

# Now MK_COMB with a dependent codomain. f = g at Pi(n:nat). vec n,
# applied to an argument equation l2 = r2 where l2 != r2 forces the
# natural codomain types vec(l2) and vec(r2) to differ.
#
# Construct a constant family `mkvec : Pi(n:nat). vec n` so REFL
# gives us |- mkvec = mkvec at Pi(n:nat). vec n. Pair with the
# specialised argument equation add 0 0 = 0 (i.e. add_0_0_eq_0):
# MK_COMB now needs cod_eq witnessing vec(add 0 0) == vec(0).
print()
new_constant("mkvec", Pi(n_var, vec(n_th)))
mkvec_th = CONST("mkvec")
f_eq = REFL(mkvec_th)
# We need add_0_0_eq_0 tagged at nat (it already is).
try:
    # First show the call fails without cod_eq:
    MK_COMB(f_eq, add_0_0_eq_0)
except HolError as e:
    print("without cod_eq ::", str(e).splitlines()[0])
bridged = MK_COMB(f_eq, add_0_0_eq_0, cod_eq=vec_bridge)
print("MK_COMB with cod_eq ::", bridged)

# ----------------------------------------------------------------
# Primitive `==>` and Rule D (dependent implication typing).
# Example 3 from the paper, adapted: x = y ⇒ f x = f y where f is a
# dependent function. Type-checking the consequent f x = f y at
# type bool needs the assumption x = y to bridge vec(x) ≡ vec(y)
# (here we use add 0 0 = 0 ⇒ nil =vec(0) nil-coerced, since we have
# that bridge already).
# ----------------------------------------------------------------
print()
# Antecedent: add 0 0 = 0  (as a bool typing_thm)
ant_typing = APP(APP(CONST("=", (nat_ty,)), add00_th), zero_th)
print("antecedent F ::", _pp_tm(ant_typing._tm), ":", _pp_ty(ant_typing._ty))

# Consequent G typed under ▷F: build nil =vec(0) (nil viewed via bridge).
# The ASSUMEd equation builds a bridge whose asl mentions F; CONV
# through that bridge lifts nil's certificate, and REFL emits a thm
# whose asl tracks the dependency. Then we wrap as a bool typing_thm.
assumed_F = ASSUME(ant_typing)
bridge_under_F = TY_CONG_BASE("vec", [assumed_F])
nil_under_F = CONV(nil_th, TY_SYM(bridge_under_F))
print("nil under ▷F  ::", nil_under_F)

# Consequent term: nil =vec(add 0 0) nil  (well-typed under ▷F).
cons_eq_term = APP(
    APP(CONST("=", (nil_under_F._ty,)), nil_under_F),
    nil_under_F,
)
print("consequent G typing ::", cons_eq_term)

# IMP_TYPE discharges F from the consequent's asl.
imp_typing = IMP_TYPE(ant_typing, cons_eq_term)
print("F ⇒ G typing ::", imp_typing)
print("            asl =", imp_typing._asl)  # F should be gone

# Now exercise the validity-layer pair. Build `[F] |- G` as a thm,
# DISCH F to get `|- F ⇒ G`, then MP-apply with an axiom that
# provides F.
#
# Pre-DISCH normalisation: g_under_F's equation is tagged at the
# bridged type vec(add 0 0), but the inner nil terms are intrinsically
# vec(0). basics_dhol's DISCH (and MP) walk the conclusion's intrinsic
# structure via TYPE_OF, so the equation must be retagged at the
# intrinsic side first. EQ_TY_CONV does that retag at the validity
# layer; the bridge moves from the term's `=` constant into the asl.
g_under_F = REFL(nil_under_F)              # [F] |- nil =_vec(add 0 0) nil
print("[F] |- G (bridged) ::", g_under_F)
g_normalised = EQ_TY_CONV(g_under_F, bridge_under_F)  # [F] |- nil =_vec(0) nil
print("[F] |- G (clean)   ::", g_normalised)
imp_thm = DISCH(ant_typing, g_normalised)
print("DISCH F   ::", imp_thm)

# Now MP with the axiom add_0_0_eq_0 (which is [] |- add 0 0 = 0).
g_thm = MP(imp_thm, add_0_0_eq_0)
print("MP(F⇒G, F) ::", g_thm)

# ----------------------------------------------------------------
# Unified declaration context: rank-1 polymorphism interleaved with
# dependent term parameters. Declare
#
#   pvec : (u:Type, n:nat) -> tp        -- vector of u of length n
#   pnil : pvec(bool, 0)                -- inhabitation witness
#   pcons : Pi(u:Type). Pi(n:nat). u -> pvec(u, n) -> pvec(u, S n)
#
# This exercises a context with BOTH a Tyvar binder and a Var
# binder, demonstrating that later context entries may use earlier
# ones (here `n:nat` could in principle reference `u:Type` -- not
# exercised, but the shape is general).
# ----------------------------------------------------------------
print()
u_tv = Tyvar("u")
pvec_pnil_ty = Tyapp("pvec", (bool_ty,), (Const("0", nat_ty),))
new_type("pvec", phi=(u_tv, Var("n", nat_ty)))
new_constant("pnil", pvec_pnil_ty)

def pvec(u_ty, n_th):
    return mk_type("pvec", [u_ty, n_th])

pnil_th = CONST("pnil")
print("pnil ::", _pp_ty(pnil_th._ty))
print("pvec(nat, 0) ::", _pp_ty(pvec(nat_ty, zero_th)))
print("pvec(bool, S 0) ::", _pp_ty(pvec(bool_ty, one_th)))

# Build a value at pvec(bool, 0) (just pnil) and a wrong-arity call.
try:
    mk_type("pvec", [bool_ty])  # missing the term arg
except HolError as e:
    print("wrong arity ::", str(e).splitlines()[0])

# Wrong shape: pass a hol_type where a typing_thm is expected.
try:
    mk_type("pvec", [bool_ty, nat_ty])
except HolError as e:
    print("wrong shape ::", str(e).splitlines()[0])

# TY_CONG_BASE with mixed argument shapes: pvec(bool, add 0 0) ==
# pvec(bool, 0) via type-refl on the u slot and add_0_0_eq_0 on n.
bool_refl = TY_REFL(bool_ty)
pvec_bridge = TY_CONG_BASE("pvec", [bool_refl, add_0_0_eq_0])
print("pvec bridge ::", pvec_bridge)

# Cross-instantiation: pvec(nat, 0) == pvec(bool, 0) would need a
# non-trivial type equality on u, which we can't prove (and rightly
# so). Show that passing TY_REFL of two different types in the u
# slot via the bridge yields well-formed but distinct Tyapps.
# Instead, exercise the typing-bridge inside CONV using pvec_bridge.
pnil_at_add = CONV(pnil_th, TY_SYM(pvec_bridge))
print("pnil viewed as pvec(bool, add 0 0) ::", _pp_ty(pnil_at_add._ty))

# ----------------------------------------------------------------
# Cross-binder dependence: a Var binder whose type mentions an
# earlier Tyvar binder.
#
#   tagged : (u:Type, x:u) -> tp
#
# Here the second context entry x has type `u`, which is bound by
# the first. At use sites we substitute the chosen hol_type for u
# into x's expected type before tag-checking. This is the case the
# 2026 paper's `Φ`-contexts make routine and the old flat
# `term_params: tuple[hol_type,...]` cannot express.
# ----------------------------------------------------------------
print()
u_tv2 = Tyvar("u")
x_var2 = Var("x", u_tv2)
tagged_witness_ty = Tyapp("tagged", (nat_ty,), (Const("0", nat_ty),))
new_type("tagged", phi=(u_tv2, x_var2))
new_constant("tagzero", tagged_witness_ty)

# Use: tagged(nat, 0) is well-formed because zero_th : nat matches
# the binder type u with u := nat.
tagged_nat0 = mk_type("tagged", [nat_ty, zero_th])
print("tagged(nat, 0)  ::", _pp_ty(tagged_nat0))

# tagged(bool, nil_th) would fail: nil_th : vec(0) does not match
# the binder type u with u := bool.
try:
    mk_type("tagged", [bool_ty, zero_th])
except HolError as e:
    print("cross-dep mismatch ::", str(e).splitlines()[0])

# TY_CONG_BASE on tagged: the n-position equation's tag must be
# whatever type the earlier Tyvar slot chose. Use TY_REFL on u
# to keep the type slot at nat, and add_0_0_eq_0 (tagged at nat)
# for the x slot.
nat_refl = TY_REFL(nat_ty)
tagged_bridge = TY_CONG_BASE("tagged", [nat_refl, add_0_0_eq_0])
print("tagged bridge   ::", tagged_bridge)

# The tag-vs-prefix check actually fires: if we pick u := bool but
# supply an equation tagged at nat (add_0_0_eq_0), it's rejected.
bool_refl_again = TY_REFL(bool_ty)
try:
    TY_CONG_BASE("tagged", [bool_refl_again, add_0_0_eq_0])
except HolError as e:
    print("cross-dep cong  ::", str(e).splitlines()[0])

# ----------------------------------------------------------------
# Predicate subtypes (item 10) + collapsed Pi precondition (item 13).
#
# Pi-binder refinement is encoded by a Subtype-typed bvar:
#   λx : Subtype(y:A, F[y]).  ===  λx:A|F[x].
# RESTRICT is the value-level intro for `A|F`; thereafter APP /
# BETA / ETA / MK_COMB are unconditional (the bvar's refined type
# carries the precondition).
# ----------------------------------------------------------------
print()
F = add_0_0_eq_0._concl  # the bool term add 0 0 = 0
# Build the refined type nat | (λy. add 0 0 = 0). Here the predicate
# doesn't mention y -- F is closed -- but Subtype's structure is
# general.
y_ref = Var("y", nat_ty)
nat_F = mk_subtype(y_ref, F)
print("subtype nat|F      ::", _pp_ty(nat_F))

# RESTRICT zero into nat|F. Needs |- F[zero/y] = |- F (closed).
zero_in_F = RESTRICT(zero_th, add_0_0_eq_0, nat_F)
print("RESTRICT zero      ::", zero_in_F)

# Wrong proof: rejected.
try:
    RESTRICT(zero_th, REFL(zero_th), nat_F)
except HolError as e:
    print("RESTRICT wrong-p   ::", str(e).splitlines()[0])

# UNRESTRICT: forget the refinement.
zero_back = UNRESTRICT(zero_in_F)
print("UNRESTRICT         ::", zero_back)

# RESTRICT_PROOF: extract the proof.
zero_F_proof = RESTRICT_PROOF(zero_in_F)
print("RESTRICT_PROOF     ::", zero_F_proof)

# Build λ over the refined domain. The binder ranges over nat|F.
n_ref = Var("n", nat_F)
body_over_ref = zero_th                          # |- 0 : nat
lam_over_ref = LAMBDA(n_ref, body_over_ref)
print("λ over nat|F       ::", lam_over_ref)

# APP: argument must already be in nat|F (achieved via RESTRICT).
app_over_ref = APP(lam_over_ref, zero_in_F)
print("APP over nat|F     ::", app_over_ref)

# APP with un-refined argument: rejected (no precondition kwarg).
try:
    APP(lam_over_ref, zero_th)
except HolError as e:
    print("APP base-arg       ::", str(e).splitlines()[0])

# BETA: no precondition handling -- binder type is nat|F, redex
# type-checks unconditionally.
n_in_ref = VAR(n_ref)
redex_ref = APP(lam_over_ref, n_in_ref)
beta_over_ref = BETA(redex_ref)
print("BETA over nat|F    ::", beta_over_ref)

# ETA: similarly trivial.
t_ref_var = Var("g", lam_over_ref._ty)
eta_over_ref = ETA(VAR(t_ref_var))
print("ETA over nat|F     ::", eta_over_ref)

# MK_COMB: argument equation must already be tagged at the refined
# type. REFL on zero_in_F suffices.
f_eq_ref = REFL(lam_over_ref)
arg_eq_ref = REFL(zero_in_F)
mk_comb_over_ref = MK_COMB(f_eq_ref, arg_eq_ref)
print("MK_COMB over nat|F ::", mk_comb_over_ref)

# FORGET_TYPING: typing-layer projection -- the value-level operation
# that the now-retired subtype layer used to express. Drops the
# refinement on a value's type directly. `zero_in_F : nat|F` becomes
# `zero_via_forget : nat`. Replaces the legacy
# `SUBSUME(zero_in_F, ST_FORGET(nat|F))` idiom.
zero_via_forget = FORGET_TYPING(zero_in_F)
print("FORGET_TYPING      ::", zero_via_forget)

# ----------------------------------------------------------------
# Item 14b.1: constants with declaration-time preconditions.
#
# Declare a constant `gated : nat` whose use is gated on F. Without
# the proof, CONST refuses; with it, CONST emits a typing_thm that
# absorbs the proof's asl (here empty, since add_0_0_eq_0 is an axiom).
# ----------------------------------------------------------------
print()
new_constant("gated", nat_ty, phi=(Assume(F),))
try:
    CONST("gated")
except HolError as e:
    print("CONST no-prec     ::", str(e).splitlines()[0])
gated_th = CONST("gated", (add_0_0_eq_0,))
print("CONST with prec   ::", gated_th)

# The constant's asl tracks the proof's. If we use an assumed
# version of F (via ASSUME), the asl picks it up.
F_assumed = ASSUME(CONCL_TYPING(add_0_0_eq_0))
gated_under_F = CONST("gated", (F_assumed,))
print("CONST under ▷F    ::", gated_under_F)

# ----------------------------------------------------------------
# Item 14b.2: type families with `▷F` in their Φ-context.
#
# Declare `pos_vec : (n:nat | n = n) -> tp` -- the obligation
# `n = n` is trivially provable by REFL, but the kernel still
# demands the proof at every mk_type call site.
# ----------------------------------------------------------------
print()
n_ctx = Var("n", nat_ty)
n_self_eq = safe_mk_eq(nat_ty, n_ctx, n_ctx)
new_type("pos_vec", phi=(n_ctx, Assume(n_self_eq)))
new_constant("pos_nil", Tyapp("pos_vec", (), (Const("0", nat_ty),)))

# mk_type without the Assume proof is rejected.
try:
    mk_type("pos_vec", [zero_th])
except HolError as e:
    print("pos_vec missing   ::", str(e).splitlines()[0])

# With the proof: pos_vec(0) is well-formed.
proof_0_eq_0 = REFL(zero_th)  # |- 0 = 0 at nat
pos_vec_0 = mk_type("pos_vec", [zero_th, proof_0_eq_0])
print("pos_vec(0)        ::", _pp_ty(pos_vec_0))

# Wrong proof (a different equation) is rejected.
one_one_eq = REFL(one_th)  # |- (S 0) = (S 0)
try:
    mk_type("pos_vec", [zero_th, one_one_eq])
except HolError as e:
    print("pos_vec wrong     ::", str(e).splitlines()[0])

# TY_CONG_BASE on pos_vec where n varies: the Assume formula
# `n = n` substitutes differently on the LHS (where n := add 0 0)
# vs the RHS (where n := 0), and the kernel correctly refuses --
# this case requires a per-side discharge that the rule doesn't
# support yet.
try:
    TY_CONG_BASE("pos_vec", [add_0_0_eq_0, REFL(add00_th)])
except HolError as e:
    print("pos_vec cong (varying n) ::", str(e).splitlines()[0])

# Now declare a second family with an *n-independent* Assume
# obligation. Then LHS and RHS substitutions coincide and
# TY_CONG_BASE proceeds normally.
pos_vec2_witness = Tyapp("pos_vec2", (), (Const("0", nat_ty),))
new_type("pos_vec2", phi=(Var("n", nat_ty), Assume(F)))  # F = (add 0 0 = 0)
new_constant("pos_nil2", pos_vec2_witness)
# mk_type at pos_vec2(0) discharges F via add_0_0_eq_0.
pv2_zero = mk_type("pos_vec2", [zero_th, add_0_0_eq_0])
print("pos_vec2(0)              ::", _pp_ty(pv2_zero))
# Congruence: pos_vec2(add 0 0) == pos_vec2(0), with the same
# n-free Assume discharge on both sides.
pos_vec2_cong = TY_CONG_BASE(
    "pos_vec2", [add_0_0_eq_0, add_0_0_eq_0]
)
print("pos_vec2 bridge          ::", pos_vec2_cong)

# ----------------------------------------------------------------
# Staged term-side declarations: a constant whose Φ includes a Var
# entry. `inc(n:nat) : nat` carries its term parameter in the Φ
# rather than being curried via Pi(n:nat). nat. Calling sites use
# CONST(name, sigma=(...)) to fill in the parameter in one step.
# ----------------------------------------------------------------
print()
n_inc = Var("n", nat_ty)
new_constant("inc", nat_ty, phi=(n_inc,))
inc_at_0 = CONST("inc", sigma=(zero_th,))
print("inc(0) (staged)   ::", inc_at_0)
inc_at_n = CONST("inc", sigma=(VAR(n_inc),))
print("inc(n) (free var) ::", inc_at_n)

# Differ-by-Var-arg: two `inc` constants with different σ-Var-arg
# are NOT alpha-equal, even though they share name + instantiated ty.
print("inc(0) tm == inc(n) tm ::",
      _tm_alpha([], inc_at_0._tm, inc_at_n._tm))

# Φ-staged definition. `dbl(n:nat) := add n n` -- the body mentions
# the Var-bound n freely; the emitted defining equation is tagged at
# the Var-binder Φ-application.
print()
dbl_body = APP(APP(add_th, VAR(n_inc)), VAR(n_inc))  # |- add n n : nat
dbl_def = new_basic_definition(
    Var("dbl", nat_ty), dbl_body, phi=(n_inc,)
)
print("dbl(n) := add n n ::", dbl_def)

# Use the staged constant: CONST("dbl", sigma=(zero_th,)) builds
# `dbl(0) : nat` with term_args=(0,).
dbl_at_0 = CONST("dbl", sigma=(zero_th,))
print("dbl(0) (staged)   ::", dbl_at_0)

# Φ with an Assume entry on a term constant: `gated_inc(n:nat |
# add 0 0 = 0) : nat`. Discharging the Assume at use site flows
# through `sigma=(...)`.
print()
new_constant(
    "gated_inc", nat_ty, phi=(n_inc, Assume(F))
)
gated_inc_at_0 = CONST(
    "gated_inc", sigma=(zero_th, add_0_0_eq_0)
)
print("gated_inc(0)      ::", gated_inc_at_0)

# ----------------------------------------------------------------
# TM_CONG_BASE: term-side congruence for a staged constant. From
# add 0 0 = 0 (per-slot Var-arg equation) derive
#   |- inc(add 0 0) = inc(0)   tagged at nat.
# The analogue of TY_CONG_BASE for term constants -- the gap that
# closed the term/type-side symmetry.
# ----------------------------------------------------------------
print()
inc_cong = TM_CONG_BASE("inc", [add_0_0_eq_0])
print("inc(add 0 0) = inc(0) ::", inc_cong)

# Multi-slot example: dbl(n) := add n n. TM_CONG_BASE on a Var-only
# Φ derives dbl(add 0 0) = dbl(0) without going through MK_COMB on
# the Pi-encoded body.
dbl_cong = TM_CONG_BASE("dbl", [add_0_0_eq_0])
print("dbl(add 0 0) = dbl(0) ::", dbl_cong)

# ----------------------------------------------------------------
# Staged theorems: (Φ) ▷ F as a first-class shape on axioms.
#
# Exercise each slot species: Tyvar (polymorphism), Var (dependent
# term parameter), Assume (precondition). `interpret(staged, σ)`
# fans the three discharge axes in one step; THM_CONG_BASE relates
# two interpretations σ_l / σ_r via per-slot equations.
# ----------------------------------------------------------------
print()

# Polymorphic axiom over a Tyvar slot. Declare a polymorphic
# `default : Pi(A:tp). A` constant, then state the axiom
#   (A:tp) ▷ default(A) = default(A)
# (trivially true, but it exercises the Tyvar slot of new_axiom).
A_tv = Tyvar("A")
new_constant("default", A_tv, phi=(A_tv,))
default_A = CONST("default", (A_tv,))
eq_A = APP(APP(CONST("=", (A_tv,)), default_A), default_A)
poly_ax = new_axiom(eq_A, phi=(A_tv,))
print("poly axiom        ::", poly_ax)
# Interpret at A := nat: |- default(nat) = default(nat).
poly_at_nat = interpret(poly_ax, (nat_ty,))
print("interpret @ nat   ::", poly_at_nat)
# Interpret at A := bool: |- default(bool) = default(bool).
poly_at_bool = interpret(poly_ax, (bool_ty,))
print("interpret @ bool  ::", poly_at_bool)

# Dependent axiom over an Assume slot. State the conditional
# axiom (n:nat, ▷ add 0 n = 0) ▷ n = 0. The Assume entry's formula
# joins the underlying thm's asl; interpret(σ) discharges it via
# the σ-entry that proves the formula at the chosen n.
n_eq_form = APP(APP(CONST("=", (nat_ty,)), add_0_n), zero_th)
inner_eq = APP(APP(CONST("=", (nat_ty,)), VAR(n_var)), zero_th)
F_assume = Assume(n_eq_form._tm)
cond_ax = new_axiom(inner_eq, phi=(n_var, F_assume))
print("cond axiom        ::", cond_ax)
# Interpret at n := 0 with a proof that add 0 0 = 0 (via add_0_0_eq_0).
# The Assume formula at n := 0 is `add 0 0 = 0`, which add_0_0_eq_0
# proves -- so the result discharges the precondition.
cond_at_0 = interpret(cond_ax, (zero_th, add_0_0_eq_0))
print("interpret σ = (0, |- add 0 0 = 0) ::", cond_at_0)

# THM_CONG_BASE: from per-slot equations relate two interpretations
# of `add_zero` (the staged axiom (n:nat) ▷ add 0 n = n). With the
# per-slot equation `add 0 0 = 0` on the n slot, derive
#     |- (add 0 (add 0 0) = add 0 0) = (add 0 0 = 0)     at bool.
add_zero_cong = THM_CONG_BASE(add_zero, [add_0_0_eq_0])
print("THM_CONG_BASE     ::", add_zero_cong)

# Empty Φ (no slots) -- the staged form degenerates to a plain thm.
triv_ax = new_axiom(
    APP(APP(CONST("=", (nat_ty,)), zero_th), zero_th)
)
print("empty-Φ axiom     ::", triv_ax)
print("interpret ()      ::", interpret(triv_ax, ()))

# Unified `instantiate` dispatcher: same σ-shape, three J-levels.
inst_type = instantiate("vec", [zero_th])          # hol_type
inst_const = instantiate("0", ())                  # typing_thm
inst_thm = instantiate(add_zero, (zero_th,))       # thm
print("instantiate vec  ::", _pp_ty(inst_type))
print("instantiate 0    ::", inst_const)
print("instantiate axiom::", inst_thm)

# Rejection paths: shape mismatch (σ arity), wrong slot evidence,
# and unbound free var in F.
try:
    interpret(add_zero, ())
except HolError as e:
    print("interpret wrong arity ::", str(e).splitlines()[0])
try:
    interpret(add_zero, (nat_ty,))  # Tyvar arg for a Var slot
except HolError as e:
    print("interpret wrong shape ::", str(e).splitlines()[0])
try:
    # unbound free var: F has `n` but Φ is empty.
    new_axiom(eq_form)
except HolError as e:
    print("axiom unbound var     ::", str(e).splitlines()[0])


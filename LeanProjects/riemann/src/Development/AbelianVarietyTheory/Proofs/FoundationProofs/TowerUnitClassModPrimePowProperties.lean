import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.ClsMod

variable {l : ℕ} [Fact l.Prime] {G : Type} [AddCommGroup G]

abbrev Q (l : ℕ) [Fact l.Prime] (n : ℕ) (G : Type) [AddCommGroup G] : Type :=
  (ℤ_[l] ⊗[ℤ] G) ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] G)))

theorem idl_pow_eq_ker (n : ℕ) : (idl l) ^ n = RingHom.ker (PadicInt.toZModPow (p := l) n) := by
  rw [PadicInt.ker_toZModPow, Ideal.span_singleton_pow]

theorem smul_mem_of_toZModPow {n : ℕ} {a : ℤ_[l]} (ha : PadicInt.toZModPow n a = 0) (m : ℤ_[l] ⊗[ℤ] G) :
    a • m ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] G)) :=
  Submodule.smul_mem_smul (by rw [idl_pow_eq_ker]; exact ha) trivial

instance neZero_pow (n : ℕ) : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem mk_tmul (n : ℕ) (c : ℤ_[l]) (g : G) :
    (Submodule.Quotient.mk (c ⊗ₜ[ℤ] g) : Q l n G) =
      Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] (((PadicInt.toZModPow n c).val : ℕ) • g)) := by
  rw [Submodule.Quotient.eq]
  have h : c ⊗ₜ[ℤ] g - (1 : ℤ_[l]) ⊗ₜ[ℤ] (((PadicInt.toZModPow n c).val : ℕ) • g)
      = (c - ((PadicInt.toZModPow n c).val : ℤ_[l])) • ((1 : ℤ_[l]) ⊗ₜ[ℤ] g) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.sub_tmul, ← TensorProduct.smul_tmul,
      nsmul_eq_mul, mul_one]
  rw [h]
  apply smul_mem_of_toZModPow
  rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]

theorem exists_mk (n : ℕ) (y : Q l n G) : ∃ g : G, Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] g) = y := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c g => exact ⟨_, (mk_tmul n c g).symm⟩
  | add x y hx hy =>
    obtain ⟨gx, hx⟩ := hx
    obtain ⟨gy, hy⟩ := hy
    exact ⟨gx + gy, by rw [TensorProduct.tmul_add, Submodule.Quotient.mk_add, hx, hy, Submodule.Quotient.mk_add]⟩

abbrev H (l n : ℕ) (G : Type) [AddCommGroup G] : AddSubgroup G := (nsmulAddMonoidHom (α := G) (l ^ n)).range

def psi (n : ℕ) : ℤ_[l] →+ (G →+ G ⧸ H l n G) :=
  (ZMod.lift (l ^ n) ⟨zmultiplesHom (G →+ G ⧸ H l n G) (QuotientAddGroup.mk' (H l n G)), by
    ext g
    simp only [zmultiplesHom_apply, AddMonoidHom.zsmul_apply, QuotientAddGroup.mk'_apply, AddMonoidHom.zero_apply]
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨g, by rw [nsmulAddMonoidHom_apply, ← natCast_zsmul, Nat.cast_pow]⟩⟩).comp (PadicInt.toZModPow n).toAddMonoidHom

theorem psi_one (n : ℕ) (g : G) : psi (l := l) n 1 g = QuotientAddGroup.mk g := by
  have e : (1 : ZMod (l ^ n)) = ((1 : ℤ) : ZMod (l ^ n)) := by simp
  simp only [psi, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_one]
  rw [e, ZMod.lift_coe]
  simp

def phi (n : ℕ) : ℤ_[l] ⊗[ℤ] G →+ G ⧸ H l n G :=
  TensorProduct.liftAddHom (psi n) (fun r c g => by rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul])

theorem phi_tmul (n : ℕ) (c : ℤ_[l]) (g : G) : phi n (c ⊗ₜ[ℤ] g) = psi n c g :=
  TensorProduct.liftAddHom_tmul _ _ _ _

theorem phi_eq_zero (n : ℕ) (x : ℤ_[l] ⊗[ℤ] G) (hx : x ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] G))) :
    phi n x = 0 := by
  refine Submodule.smul_induction_on hx (fun a ha m hm => ?_) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
  clear hm
  rw [idl_pow_eq_ker, RingHom.mem_ker] at ha
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul c g =>
    rw [TensorProduct.smul_tmul', phi_tmul, smul_eq_mul]
    simp [psi, ha]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]

theorem mk_eq_iff (n : ℕ) (g g' : G) :
    (Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] g) : Q l n G) = Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] g') ↔
      ∃ h : G, g = g' + (l ^ n) • h := by
  constructor
  · intro e
    rw [Submodule.Quotient.eq, ← TensorProduct.tmul_sub] at e
    have h0 := phi_eq_zero n _ e
    rw [phi_tmul, psi_one, QuotientAddGroup.eq_zero_iff] at h0
    obtain ⟨h, hh⟩ := h0
    refine ⟨h, ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hh
    rw [hh]; abel
  · rintro ⟨h, rfl⟩
    rw [Submodule.Quotient.eq, ← TensorProduct.tmul_sub, add_sub_cancel_left, TensorProduct.tmul_smul,
      ← Nat.cast_smul_eq_nsmul ℤ_[l]]
    apply smul_mem_of_toZModPow
    rw [map_natCast, ZMod.natCast_self]

end GlobalTheory.KZ.ClsMod

open GlobalTheory.KZ.ClsMod in

theorem GlobalTheory.KZ.H3.cls_props : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, (∀ y, ∃ f, X.cls l n f = y) ∧ (∀ f f' : X.Kˣ, X.cls l n f = X.cls l n f' ↔ ∃ g : X.Kˣ, f = f' * g ^ (l ^ n)) ∧ (∀ f f' : X.Kˣ, X.cls l n (f * f') = X.cls l n f + X.cls l n f') ∧ X.cls l n 1 = 0 ∧ (∀ (c : ℤ_[l]) (f : X.Kˣ), c • X.cls l n f = X.cls l n (f ^ (PadicInt.toZModPow n c).val)) ∧ (∀ (φ : X.K ≃+* X.K) (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f → AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = X.cls l n (Units.map φ.toMonoidHom f)) ∧ (∀ (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x = X.cls l (n + 1) f → AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) := by
  intro Ω _ _ ε X l _ n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨g, hg⟩ := exists_mk n y
    exact ⟨Additive.toMul g, hg⟩
  · intro f f'
    unfold Tower.cls
    rw [mk_eq_iff]
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨Additive.toMul h, ?_⟩
      apply Additive.ofMul.injective
      rw [hh, ofMul_mul, ofMul_pow]; rfl
    · rintro ⟨g, rfl⟩
      exact ⟨Additive.ofMul g, by rw [ofMul_mul, ofMul_pow]⟩
  · intro f f'
    unfold Tower.cls
    rw [ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]
  · unfold Tower.cls
    rw [ofMul_one, TensorProduct.tmul_zero, Submodule.Quotient.mk_zero]
  · intro c f
    unfold Tower.cls
    rw [← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, mk_tmul, ofMul_pow]
  · intro φ x f hx
    rw [AdicCompletion.eval_apply] at hx ⊢
    have e := AdicCompletion.map_val_apply (idl l)
      (LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))) (n := n) x
    refine (e.trans ?_)
    rw [hx, Tower.cls, LinearMap.reduceModIdeal_apply, LinearMap.baseChange_tmul]
    rfl
  · intro x f hx
    rw [AdicCompletion.eval_apply] at hx ⊢
    rw [← AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) x, hx]
    rfl

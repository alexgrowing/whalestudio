import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory

open TensorProduct

theorem tensor_padic_cls_eq {G : Type} [CommGroup G] (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : G)
    (h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul f' - (1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul f) ∈
      ((Ideal.span {(l : ℤ_[l])}) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] Additive G)))) :
    ∃ u : G, f' = f * u ^ (l ^ n) := by
  classical
  let M := Additive G
  let P : Submodule ℤ M := LinearMap.range (DistribMulAction.toLinearMap ℤ M (((l : ℤ)) ^ n))
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hkill : ∀ q : M ⧸ P, (l ^ n) • q = 0 := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨m, by change ((l : ℤ) ^ n) • m = l ^ n • m; rw [← Nat.cast_pow, natCast_zsmul]⟩
  letI : Module (ZMod (l ^ n)) (M ⧸ P) := AddCommGroup.zmodModule hkill
  let B : ℤ_[l] →ₗ[ℤ] M →ₗ[ℤ] M ⧸ P :=
    LinearMap.mk₂ ℤ (fun c m => (PadicInt.toZModPow n c) • P.mkQ m)
      (fun c c' m => by simp [add_smul])
      (fun k c m => by
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)), ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)),
          smul_smul, smul_eq_mul])
      (fun c m m' => by simp [smul_add])
      (fun k c m => by
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)), ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)),
          smul_smul, smul_smul, mul_comm])
  let φ : ℤ_[l] ⊗[ℤ] M →ₗ[ℤ] M ⧸ P := TensorProduct.lift B
  have hφ : ∀ c m, φ (c ⊗ₜ m) = (PadicInt.toZModPow n c) • P.mkQ m := fun c m => by
    exact TensorProduct.lift.tmul (f' := B) c m
  have hI : (Ideal.span {(l : ℤ_[l])}) ^ n = RingHom.ker (PadicInt.toZModPow (p := l) n) := by
    rw [PadicInt.ker_toZModPow, Ideal.span_singleton_pow]
  have hzero : ∀ x ∈ ((Ideal.span {(l : ℤ_[l])}) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] M))), φ x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    rw [hI, RingHom.mem_ker] at hr
    clear hy
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, hφ, map_mul, hr, zero_mul, zero_smul]
    | add a b ha hb => rw [smul_add, map_add, ha, hb, add_zero]
  have h0 := hzero _ h
  rw [map_sub, hφ, hφ, map_one, one_smul, one_smul, sub_eq_zero, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq] at h0
  obtain ⟨y, hy⟩ := h0
  refine ⟨Additive.toMul y, ?_⟩
  have hy' : Additive.toMul (((l : ℤ) ^ n) • y) = f' / f := by
    have hy2 : ((l : ℤ) ^ n) • y = Additive.ofMul f' - Additive.ofMul f := hy
    rw [hy2]; rfl
  rw [toMul_zsmul] at hy'
  rw [← div_eq_iff_eq_mul', ← hy']
  norm_cast

theorem Tower.cls_eq_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (f f' : X.Kˣ) (h : X.cls l n f = X.cls l n f') :
    ∃ u : X.Kˣ, (f' : X.K) = f * (u : X.K) ^ (l ^ n) := by
  unfold Tower.cls at h
  rw [Submodule.Quotient.eq'] at h
  obtain ⟨u, hu⟩ := tensor_padic_cls_eq l n f f' (by simpa [neg_add_eq_sub] using h)
  exact ⟨u, by rw [hu]; push_cast; rfl⟩

end GlobalTheory

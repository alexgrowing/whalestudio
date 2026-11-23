import Development.EtaleCohomology.KummerTheory.SHInsepPf

noncomputable section
open scoped TensorProduct
open Polynomial

namespace LateralTheory.KummerTheory

section
variable (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A]

theorem shInsepRes_pow [Nontrivial (A ⊗[κ] K)] (y : A ⊗[κ] K) :
    ∃ n : ℕ, ∃ a : A, y ^ (ringExpChar κ) ^ n = algebraMap A (A ⊗[κ] K) a := by
  set q := ringExpChar κ
  have : ExpChar (A ⊗[κ] K) q :=
    expChar_of_injective_algebraMap (algebraMap κ (A ⊗[κ] K)).injective q
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a k =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem κ q k
    refine ⟨n, c • a ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc]
    show (a ^ q ^ n) ⊗ₜ[κ] (algebraMap κ K c) = (c • a ^ q ^ n) ⊗ₜ[κ] (1 : K)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨n, a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := hy
    refine ⟨n + m, a ^ q ^ m + b ^ q ^ n, ?_⟩
    rw [add_pow_expChar_pow, map_add, map_pow, map_pow, ← ha, ← hb, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add, add_comm m n]

omit [IsPurelyInseparable κ K] in
theorem shInsepRes_inj : Function.Injective (algebraMap A (A ⊗[κ] K)) :=
  Algebra.TensorProduct.includeLeft_injective (S := A) (algebraMap κ K).injective

theorem shInsepRes_localHom [Nontrivial (A ⊗[κ] K)] : IsLocalHom (algebraMap A (A ⊗[κ] K)) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨u, hu⟩ := ha
  obtain ⟨n, b, hb⟩ := shInsepRes_pow κ K A (↑u⁻¹ : A ⊗[κ] K)
  have hQ : (ringExpChar κ) ^ n ≠ 0 := pow_ne_zero _ (expChar_pos κ (ringExpChar κ)).ne'
  have h1 : algebraMap A (A ⊗[κ] K) (a ^ (ringExpChar κ) ^ n * b) = algebraMap A (A ⊗[κ] K) 1 := by
    rw [map_mul, map_pow, ← hb, ← hu, ← mul_pow, Units.mul_inv, one_pow, map_one]
  have h2 := shInsepRes_inj κ K A h1
  exact (isUnit_pow_iff hQ).mp (isUnit_of_mul_isUnit_left (h2 ▸ isUnit_one))

end

theorem SHInsepRes_of : SHInsepRes := by
  intro κ K A _ _ _ _ _ _ hA _
  obtain ⟨hh, hsc⟩ := hA
  have : IsLocalRing A := hh.toIsLocalRing
  have : IsLocalHom (algebraMap A (A ⊗[κ] K)) := shInsepRes_localHom κ K A
  let _ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (A ⊗[κ] K)) :=
    (IsLocalRing.ResidueField.map (algebraMap A (A ⊗[κ] K))).toAlgebra
  have : Algebra.IsAlgebraic (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (A ⊗[κ] K)) := by
    constructor
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨n, a, ha⟩ := shInsepRes_pow κ K A y
    have hQ : 0 < (ringExpChar κ) ^ n := pow_pos (expChar_pos κ (ringExpChar κ)) _
    refine ⟨X ^ (ringExpChar κ) ^ n - C (IsLocalRing.residue A a), X_pow_sub_C_ne_zero hQ _, ?_⟩
    rw [map_sub, map_pow, aeval_X, aeval_C, ← map_pow, ha, sub_eq_zero]
    rfl
  exact Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField A)

end LateralTheory.KummerTheory

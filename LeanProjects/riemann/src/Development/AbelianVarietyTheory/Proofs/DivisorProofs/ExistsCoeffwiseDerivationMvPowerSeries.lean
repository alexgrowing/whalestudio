import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

theorem mvPowerSeries_derivation_coeffwise (σ R : Type) [CommRing R] (D : Derivation ℤ R R) :
    ∃ E : Derivation ℤ (MvPowerSeries σ R) (MvPowerSeries σ R),
      ∀ F α, MvPowerSeries.coeff α (E F) = D (MvPowerSeries.coeff α F) := by
  classical
  let L : MvPowerSeries σ R →ₗ[ℤ] MvPowerSeries σ R :=
    { toFun := fun F => fun α => D (MvPowerSeries.coeff α F)
      map_add' := by
        intro F G
        funext α
        show D (MvPowerSeries.coeff α (F + G)) = D (MvPowerSeries.coeff α F) + D (MvPowerSeries.coeff α G)
        rw [map_add, map_add]
      map_smul' := by
        intro n F
        funext α
        show D (MvPowerSeries.coeff α (n • F)) = n • D (MvPowerSeries.coeff α F)
        rw [map_zsmul, map_zsmul] }
  have hL : ∀ F α, MvPowerSeries.coeff α (L F) = D (MvPowerSeries.coeff α F) := fun _ _ => rfl
  refine ⟨Derivation.mk' L ?_, ?_⟩
  · intro F G
    ext α
    rw [smul_eq_mul, smul_eq_mul, map_add]
    erw [hL]
    rw [MvPowerSeries.coeff_mul, map_sum,
      MvPowerSeries.coeff_mul, mul_comm G, MvPowerSeries.coeff_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    erw [hL, hL]
    exact congrArg (_ + ·) (mul_comm _ _)
  · intro F α
    rfl

end GlobalTheory

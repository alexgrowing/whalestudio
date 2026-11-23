import Mathlib
import ReciprocityTheory.Chebotarev.EulerSum
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory

theorem sum_absNorm_rpow_fractionalIdeal_le_le :
    ∀ (K : Type) [Field K] [NumberField K] (t : ℝ), 1 < t → ∃ Z : ℝ,
    ∀ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 →
      ∑' J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ I},
        ENNReal.ofReal ((FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) ^ (-t)) ≤
      ENNReal.ofReal (Z * (FractionalIdeal.absNorm I : ℝ) ^ (-t)) := by
  intro K _ _ t ht
  refine ⟨ReciprocityTheory.Cheb.idealZetaR K t, fun I hI => ?_⟩
  classical
  have hex : ∀ J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ I},
      ∃ b : Ideal (𝓞 K), (b : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = I⁻¹ * J.1 := by
    intro J
    refine FractionalIdeal.le_one_iff_exists_coeIdeal.mp ?_
    calc I⁻¹ * J.1 ≤ I⁻¹ * I := mul_le_mul_right J.2.2 _
      _ = 1 := inv_mul_cancel₀ hI
  choose g hg using hex
  have hJ : ∀ J, J.1 = I * (g J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    intro J; rw [hg, ← mul_assoc, mul_inv_cancel₀ hI, one_mul]
  have hinj : Function.Injective g := by
    intro J1 J2 h; apply Subtype.ext; rw [hJ J1, hJ J2, h]
  have hI0 : (0 : ℝ) ≤ (FractionalIdeal.absNorm I : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg I
  have hN : ∀ J, ((FractionalIdeal.absNorm J.1 : ℚ) : ℝ) ^ (-t) =
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ (-t) * ((Ideal.absNorm (g J) : ℕ) : ℝ) ^ (-t) := by
    intro J
    rw [hJ J, map_mul, FractionalIdeal.coeIdeal_absNorm, Rat.cast_mul, Rat.cast_natCast,
      Real.mul_rpow hI0 (Nat.cast_nonneg _)]
  refine ENNReal.summable.tsum_le_of_sum_le fun s => ?_
  have hnn : ∀ J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ I},
      0 ≤ ((FractionalIdeal.absNorm J.1 : ℚ) : ℝ) ^ (-t) := fun J =>
    Real.rpow_nonneg (by exact_mod_cast FractionalIdeal.absNorm_nonneg _) _
  rw [← ENNReal.ofReal_sum_of_nonneg (fun J _ => hnn J)]
  apply ENNReal.ofReal_le_ofReal
  simp_rw [hN]
  rw [← Finset.mul_sum, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hI0 _)
  rw [← Finset.sum_image (f := fun b : Ideal (𝓞 K) => ((Ideal.absNorm b : ℕ) : ℝ) ^ (-t))
    (fun x _ y _ h => hinj h)]
  exact ReciprocityTheory.Cheb.sum_le_idealZetaR K ht _

end GlobalTheory

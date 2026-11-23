import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubidealNormPowerSeriesBound
import Mathlib
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subideal_norm_power_series_bound : ∀ (K : Type) [Field K] [NumberField K] (t : ℝ), 1 < t → ∃ Z : ℝ,
    ∀ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 →
      ∑' J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ I},
        ENNReal.ofReal ((FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) ^ (-t)) ≤
      ENNReal.ofReal (Z * (FractionalIdeal.absNorm I : ℝ) ^ (-t)) := by
  first | exact @GlobalTheory.sum_absNorm_rpow_fractionalIdeal_le_le | exact GlobalTheory.sum_absNorm_rpow_fractionalIdeal_le_le | (intros; apply GlobalTheory.sum_absNorm_rpow_fractionalIdeal_le_le <;> assumption)

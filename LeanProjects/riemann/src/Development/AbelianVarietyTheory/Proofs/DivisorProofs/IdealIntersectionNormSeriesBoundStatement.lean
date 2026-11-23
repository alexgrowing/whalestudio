import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealIntersectionNormSeriesBound
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
theorem _root_.GlobalTheory.T.ideal_intersection_norm_series_bound : ∀ (K : Type) [Field K] [NumberField K] (I₀ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), I₀ ≠ 0 → I ≠ 0 →
    ∀ (t : ℝ) (g : K → ENNReal),
    ∑' c : {c : K // c ≠ 0}, ENNReal.ofReal ((FractionalIdeal.absNorm
        (I ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c : K)⁻¹ * I₀) : ℝ) ^ (-t)) * g c ≤
      ∑' J : {J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K // J ≠ 0 ∧ J ≤ I},
        ENNReal.ofReal ((FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) ^ (-t)) *
          ∑' c : {c : K // c ∈ I₀ / (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)}, g c := by
  first | exact @GlobalTheory.RegroupDenom.tsum_regroup_by_denominator_le | exact GlobalTheory.RegroupDenom.tsum_regroup_by_denominator_le | (intros; apply GlobalTheory.RegroupDenom.tsum_regroup_by_denominator_le <;> assumption)

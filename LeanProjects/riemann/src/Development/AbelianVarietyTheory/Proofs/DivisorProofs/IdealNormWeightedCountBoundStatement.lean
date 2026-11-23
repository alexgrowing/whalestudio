import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealNormWeightedCountBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_norm_weighted_count_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ I₀ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, I₀ ≠ 0 →
    ∀ B : InfinitePlace F → ℝ, (∀ w, 0 < B w) → ∀ s : ℝ, 2 < s → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ,
      ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (A : InfinitePlace F → ℝ), (∀ w, 0 ≤ A w) →
        δ ≤ (FractionalIdeal.absNorm I : ℝ) * ∏ w, A w →
        ∑' c : {c : E // c ≠ 0}, ENNReal.ofReal (((FractionalIdeal.absNorm
            (I ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E)⁻¹ * I₀) : ℝ) *
            ∏ w, (A w + ‖Algebra.norm w.Completion (inclR (F := F) w.Completion (c : E))‖ * B w)) ^ (-s)) ≤
          ENNReal.ofReal C * ENNReal.ofReal (((FractionalIdeal.absNorm I : ℝ) * ∏ w, A w) ^ (1 - s)) := by
  first | exact @GlobalTheory.IdealBoxSum.lattice_sum_le | exact GlobalTheory.IdealBoxSum.lattice_sum_le | (intros; apply GlobalTheory.IdealBoxSum.lattice_sum_le <;> assumption)

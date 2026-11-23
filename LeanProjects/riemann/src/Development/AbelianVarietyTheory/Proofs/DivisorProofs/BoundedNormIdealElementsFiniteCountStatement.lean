import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedNormIdealElementsFiniteCount
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
theorem _root_.GlobalTheory.T.bounded_norm_ideal_elements_finite_count : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∃ C : ℝ, ∀ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔞 ≠ 0 →
      ∀ T : InfinitePlace F → ℝ, (∀ w, 0 ≤ T w) →
        {c : E | c ∈ 𝔞 ∧ ∀ w, ‖Algebra.norm w.Completion (inclR (F := F) w.Completion c)‖ ≤ T w}.Finite ∧
        ({c : E | c ∈ 𝔞 ∧ ∀ w, ‖Algebra.norm w.Completion (inclR (F := F) w.Completion c)‖ ≤ T w}.ncard : ℝ) ≤
          1 + C * (∏ w, T w) / (FractionalIdeal.absNorm 𝔞 : ℝ) := by
  first | exact @GlobalTheory.CountBox.count_ideal_points | exact GlobalTheory.CountBox.count_ideal_points | (intros; apply GlobalTheory.CountBox.count_ideal_points <;> assumption)

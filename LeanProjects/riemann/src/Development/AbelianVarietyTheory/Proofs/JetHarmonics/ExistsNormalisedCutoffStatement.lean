import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedCutoff
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_cutoff' : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μS : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM S μS → PI.IsRightInvM S μS → ∃ φ : PI.MtM m → ℝ≥0∞, Measurable φ ∧ ∀ x : PI.MtM m, Matrix.of x ∈ G → ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1 := by
  first | exact @GlobalTheory.exists_normalised_cutoff | exact GlobalTheory.exists_normalised_cutoff | (intros; apply GlobalTheory.exists_normalised_cutoff <;> assumption)

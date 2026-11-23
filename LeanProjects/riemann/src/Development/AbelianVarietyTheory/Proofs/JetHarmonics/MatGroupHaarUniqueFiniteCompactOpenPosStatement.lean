import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos : ∀ (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsHaarOnM G μ → (∀ μ' : Measure (PI.MtM m), PI.IsHaarOnM G μ' → ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ μ' = c • μ) ∧ (∀ K : Set (PI.MtM m), IsCompact K → (∀ x ∈ K, Matrix.of x ∈ G) → μ K < ⊤) ∧ ∀ U : Set (PI.MtM m), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ G) → 0 < μ U := by
  first | exact @GlobalTheory.MatHaar.haar_unique_locFinite_openPos | exact GlobalTheory.MatHaar.haar_unique_locFinite_openPos | (intros; apply GlobalTheory.MatHaar.haar_unique_locFinite_openPos <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelRegionNormBound
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_region_norm_bound : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', ∀ b : Fin (r + 1), eucl (s *ᵥ fvec k r z b) ≤ C0 * opn (s * γ * s'⁻¹) ^ (r * (r + 1)) ∧ eucl (s' *ᵥ fvec k r z' b) ≤ C0 * opn (s * γ * s'⁻¹) ^ (r * (r + 1)) := by
  first | exact @GlobalTheory.SgInf.frame_image_bound | exact GlobalTheory.SgInf.frame_image_bound | (intros; apply GlobalTheory.SgInf.frame_image_bound <;> assumption)

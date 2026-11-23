import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsFolnerSequenceBessel
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isFolnerSequenceBessel : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μS : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (Sset k r z) μS → ∃ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om := by
  first | exact @GlobalTheory.SgInf.FolnerSets.exists_isFolner | exact GlobalTheory.SgInf.FolnerSets.exists_isFolner | (intros; apply GlobalTheory.SgInf.FolnerSets.exists_isFolner <;> assumption)

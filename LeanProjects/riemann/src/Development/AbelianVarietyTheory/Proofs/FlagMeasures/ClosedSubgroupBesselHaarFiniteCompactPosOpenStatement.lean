import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn S μ → (∀ C : Set (Mt k r), IsCompact C → μ C < ⊤) ∧ (∀ U : Set (Mt k r), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ S) → 0 < μ U) := by
  first | exact @GlobalTheory.SgInf.haarOn_locFinite_openPos | exact GlobalTheory.SgInf.haarOn_locFinite_openPos | (intros; apply GlobalTheory.SgInf.haarOn_locFinite_openPos <;> assumption)

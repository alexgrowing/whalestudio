import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → IsClosedSub k r (GG k r) ∧ IsClosedSub k r (Nset k r) ∧ IsClosedSub k r (UWset k r z) ∧ IsClosedSub k r (Sset k r z) ∧ IsCompact (UWset k r z) := by
  first | exact @GlobalTheory.SgInf.closedSub_groups | exact GlobalTheory.SgInf.closedSub_groups | (intros; apply GlobalTheory.SgInf.closedSub_groups <;> assumption)

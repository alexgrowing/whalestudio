import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapRigidity
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_map_rigidity : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → RigidityProps B τ := by
  first | exact @GlobalTheory.FlatRigidity.rigidity | exact GlobalTheory.FlatRigidity.rigidity | (intros; apply GlobalTheory.FlatRigidity.rigidity <;> assumption)

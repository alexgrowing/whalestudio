import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormTypeOneOne
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_form_type_one_one : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ P ∈ cov B g, ∀ v w : Pt E g, om0 τ P ![Complex.I • v, Complex.I • w] = om0 τ P ![v, w] := by
  first | exact @GlobalTheory.FlatTypeOneOne.om0_I_smul | exact GlobalTheory.FlatTypeOneOne.om0_I_smul | (intros; apply GlobalTheory.FlatTypeOneOne.om0_I_smul <;> assumption)

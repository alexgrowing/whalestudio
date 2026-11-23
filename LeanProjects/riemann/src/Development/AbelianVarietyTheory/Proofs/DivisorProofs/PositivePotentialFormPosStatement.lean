import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositivePotentialFormPos
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_potential_form_pos : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsPotential A P → IsPosPot A P → IsCompatChart A ψ → ∀ z ∈ ψ.target, ∀ w : Fin e → ℂ, w ≠ 0 → 0 < formAt ψ P z w := by
  first | exact @GlobalTheory.formAt_pos_of_isPosPot | exact GlobalTheory.formAt_pos_of_isPosPot | (intros; apply GlobalTheory.formAt_pos_of_isPosPot <;> assumption)

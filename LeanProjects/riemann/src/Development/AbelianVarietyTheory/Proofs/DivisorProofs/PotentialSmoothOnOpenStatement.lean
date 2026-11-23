import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOnOpen
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potential_smooth_on_open : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X) (O : Set X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (z : Fin e → ℂ), IsOpen O → IsPotentialOn A O P → IsCompatChart A ψ → z ∈ ψ.target → ψ.symm z ∈ O → ContDiffAt ℝ 2 (P.φ (ψ.symm z) ∘ ψ.symm) z := by
  first | exact @GlobalTheory.isPotentialOn_contDiffAt_two_compatChart | exact GlobalTheory.isPotentialOn_contDiffAt_two_compatChart | (intros; apply GlobalTheory.isPotentialOn_contDiffAt_two_compatChart <;> assumption)

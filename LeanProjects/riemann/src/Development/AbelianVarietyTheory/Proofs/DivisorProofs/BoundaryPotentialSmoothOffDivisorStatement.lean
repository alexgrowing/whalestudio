import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialSmoothOffDivisor
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_potential_smooth_off_divisor : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X), IsBoundary A L s D → ∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ D i → ContDiffAt ℝ ∞ (rComp L s i ∘ ψ.symm) z := by
  first | exact @GlobalTheory.rComp_contDiffAt_compatChart | exact GlobalTheory.rComp_contDiffAt_compatChart | (intros; apply GlobalTheory.rComp_contDiffAt_compatChart <;> assumption)

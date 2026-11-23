import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormTwoSidedBound
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_form_two_sided_bound : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (K : LocPot X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (Kc C7 c : ℝ), IsPotential A K → IsBoundary A L s D → IsOpen (⋃ i, D i)ᶜ → ScalarBounds L s D → 0 < Kc → (∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ ⋃ j, D j → ∀ w, |ddcAt ψ (rComp L s i) z w| ≤ Kc * formAt ψ K z w) → (∀ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ → ∀ z ∈ ψ.target, ∀ w, 0 ≤ formAt ψ K z w) → 0 < C7 → (∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ ⋃ j, D j → ∀ w, gradSqAt ψ (rComp L s i) z w ≤ C7 * Real.exp (rComp L s i (ψ.symm z)) * formAt ψ K z w) → 0 < c → TwoSided A K L s D c → ∃ C : ℝ, 0 < C ∧ GrowthBounds A K L s D c C := by
  first | exact @GlobalTheory.PoincareGrowth.growthBounds | exact GlobalTheory.PoincareGrowth.growthBounds | (intros; apply GlobalTheory.PoincareGrowth.growthBounds <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormBoundOfDdc
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_form_bound_of_ddc : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (K : LocPot X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (Kc c : ℝ), IsPotential A K → IsBoundary A L s D → 0 < Kc → (∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ ⋃ j, D j → ∀ w, |ddcAt ψ (rComp L s i) z w| ≤ Kc * formAt ψ K z w) → (∀ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ → ∀ z ∈ ψ.target, ∀ w, 0 ≤ formAt ψ K z w) → 0 < c → 2 * c * m * Kc ≤ Real.exp 1 → TwoSided A K L s D c := by
  first | exact @GlobalTheory.poincare_twoSided | exact GlobalTheory.poincare_twoSided | (intros; apply GlobalTheory.poincare_twoSided <;> assumption)

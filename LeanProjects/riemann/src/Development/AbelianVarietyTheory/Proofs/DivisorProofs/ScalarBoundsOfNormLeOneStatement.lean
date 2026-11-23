import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarBoundsOfNormLeOne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_bounds_of_norm_le_one : ∀ {X : Type} [TopologicalSpace X] {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X), (∀ i y, normSec (L i) (s i) y ≤ 1) → (∀ y, y ∉ ⋃ i, D i → ∀ i, normSec (L i) (s i) y ≠ 0) → ScalarBounds L s D := by
  first | exact @GlobalTheory.Proof.scalarBounds_of_norm_le_one | exact GlobalTheory.Proof.scalarBounds_of_norm_le_one | (intros; apply GlobalTheory.Proof.scalarBounds_of_norm_le_one <;> assumption)

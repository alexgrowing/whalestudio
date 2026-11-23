import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryNormZeroIffOpenCompl
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_norm_zero_iff_open_compl : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X), IsBoundary A L s D → (∀ i y, normSec (L i) (s i) y = 0 ↔ y ∈ D i) ∧ IsOpen (⋃ i, D i)ᶜ := by
  first | exact @GlobalTheory.Proof.boundary_norm_zero_iff_open_compl.main | exact GlobalTheory.Proof.boundary_norm_zero_iff_open_compl.main | (intros; apply GlobalTheory.Proof.boundary_norm_zero_iff_open_compl.main <;> assumption)

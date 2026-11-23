import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialComparableTsum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_potential_comparable_tsum : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)), IsBoundary A L s D → IsAdaptedPolydisc A D ψ σ → ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) (1 / 2), ψ.symm z ∉ ⋃ i, D i → C⁻¹ * tSum σ z ≤ rTot L s (ψ.symm z) ∧ rTot L s (ψ.symm z) ≤ C * tSum σ z := by
  first | exact @GlobalTheory.PoincareLocal.rTot_comparable_tSum | exact GlobalTheory.PoincareLocal.rTot_comparable_tSum | (intros; apply GlobalTheory.PoincareLocal.rTot_comparable_tSum <;> assumption)

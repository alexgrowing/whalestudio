import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricLocalBound
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_metric_local_bound : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (K : LocPot X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)), IsPotential A K → IsPosPot A K → IsBoundary A L s D → IsAdaptedPolydisc A D ψ σ → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∀ c : ℝ, 0 < c → TwoSided A K L s D c → ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, ψ.symm z ∉ ⋃ i, D i → ∀ w, C⁻¹ * modelAt σ z w ≤ formAt ψ (poincarePot K L s c) z w ∧ formAt ψ (poincarePot K L s c) z w ≤ C * modelAt σ z w := by
  first | exact @GlobalTheory.poincarePot_comparable_modelAt | exact GlobalTheory.poincarePot_comparable_modelAt | (intros; apply GlobalTheory.poincarePot_comparable_modelAt <;> assumption)

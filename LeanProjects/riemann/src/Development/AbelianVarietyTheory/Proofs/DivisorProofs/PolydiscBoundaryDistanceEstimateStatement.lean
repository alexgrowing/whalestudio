import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolydiscBoundaryDistanceEstimate
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSectionSmoothPolydiscStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polydisc_boundary_distance_estimate : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)), IsBoundary A L s D → IsAdaptedPolydisc A D ψ σ → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, ψ.symm z ∉ ⋃ i, D i → ∀ w : Fin e → ℂ, (∀ (i : Fin m) (k : Fin e), σ i = some k → ‖w k‖ ^ 2 ≤ ‖w k‖ ^ 2 / (‖z k‖ ^ 2 * tOf (z k) ^ 2)) ∧ ∀ i : Fin m, gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2 ≤ Option.elim (σ i) 0 (fun k => ‖w k‖ ^ 2 / (‖z k‖ ^ 2 * tOf (z k) ^ 2)) + C * ∑ k, ‖w k‖ ^ 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → δ * Option.elim (σ i) 0 (fun k => ‖w k‖ ^ 2 / (‖z k‖ ^ 2 * tOf (z k) ^ 2)) / (36 * Real.pi ^ 3) - δ * C * ∑ k, ‖w k‖ ^ 2 ≤ gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2 := by
  first | exact @GlobalTheory.CompBounds.compBounds | exact GlobalTheory.CompBounds.compBounds | (intros; apply GlobalTheory.CompBounds.compBounds <;> assumption)

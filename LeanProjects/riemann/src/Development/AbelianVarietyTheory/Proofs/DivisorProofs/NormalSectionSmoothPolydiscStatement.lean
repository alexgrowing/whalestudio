import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSectionSmoothPolydisc
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_section_smooth_polydisc : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)), IsBoundary A L s D → IsAdaptedPolydisc A D ψ σ → ∀ i, ∃ f : (Fin e → ℂ) → ℝ, ContDiffOn ℝ ∞ f (Metric.ball (0 : Fin e → ℂ) 1) ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1, normSec (L i) (s i) (ψ.symm z) ^ 2 = Option.elim (σ i) 1 (fun k => ‖z k‖ ^ 2) * Real.exp (-f z) := by
  first | exact @GlobalTheory.SecFactor.factor_on_polydisc | exact GlobalTheory.SecFactor.factor_on_polydisc | (intros; apply GlobalTheory.SecFactor.factor_on_polydisc <;> assumption)

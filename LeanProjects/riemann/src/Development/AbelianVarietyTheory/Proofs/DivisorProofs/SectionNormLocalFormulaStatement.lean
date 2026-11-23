import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNormLocalFormula
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_norm_local_formula : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X), IsBoundary A L s D → ∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ D i → AnalyticAt ℂ (s i (ψ.symm z) ∘ ψ.symm) z ∧ s i (ψ.symm z) (ψ.symm z) ≠ 0 ∧ (fun y => normSec (L i) (s i) (ψ.symm y) ^ 2) =ᶠ[nhds z] (fun y => ‖(s i (ψ.symm z) ∘ ψ.symm) y‖ ^ 2 * Real.exp (-2 * ((L i).φ (ψ.symm z) ∘ ψ.symm) y)) := by
  first | exact @GlobalTheory.boundary_chart_facts | exact GlobalTheory.boundary_chart_facts | (intros; apply GlobalTheory.boundary_chart_facts <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialExtendsAcrossBoundary
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potential_extends_across_boundary : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (P : LocPot X) {m : ℕ} (D : Fin m → Set X), IsOpen (⋃ i, D i)ᶜ → IsPotentialOn A (⋃ i, D i)ᶜ P → (∀ x : X, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)), IsAdaptedPolydisc A D ψ σ ∧ x ∈ ψ.source ∧ ψ x = 0) → (∀ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)), IsAdaptedPolydisc A D ψ σ → ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, ψ.symm z ∉ ⋃ i, D i → ∀ w, C⁻¹ * modelAt σ z w ≤ formAt ψ P z w ∧ formAt ψ P z w ≤ C * modelAt σ z w) → maMeasure A (fun _ => P) (⋃ i, D i)ᶜ < ⊤ := by
  first | exact @GlobalTheory.PoincareVolume.maMeasure_compl_lt_top | exact GlobalTheory.PoincareVolume.maMeasure_compl_lt_top | (intros; apply GlobalTheory.PoincareVolume.maMeasure_compl_lt_top <;> assumption)

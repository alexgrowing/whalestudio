import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySublevelClosureComplement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_sublevel_closure_complement : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X)
    (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ a : ℝ, closure {x | x ∈ (boundary σ)ᶜ ∧ -a ≤ pFun Λ σ c x / 2} ⊆ (boundary σ)ᶜ := by
  first | exact @GlobalTheory.PFunBoundary.closure_superlevel_subset_compl | exact GlobalTheory.PFunBoundary.closure_superlevel_subset_compl | (intros; apply GlobalTheory.PFunBoundary.closure_superlevel_subset_compl <;> assumption)

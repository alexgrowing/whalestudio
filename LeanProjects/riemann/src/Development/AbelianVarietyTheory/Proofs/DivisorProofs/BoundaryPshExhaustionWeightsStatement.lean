import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPshExhaustionWeights
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_psh_exhaustion_weights : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∃ (w : ℕ → X → ℝ) (K : ℝ) (O : ℕ → Set X),
      (∀ R, A.Smooth (w R)) ∧ (∀ R, IsPsh A (α + LocPot.ofFun (w R))) ∧
      (∀ R x, x ∉ boundary σ →
        -(K * (1 + ∑ i, Real.log (rFun (Λ i) (σ i) x))) ≤ w R x ∧ w R x ≤ 0) ∧
      (∀ R, IsOpen (O R)) ∧ Monotone O ∧ (∀ R, O R ⊆ (boundary σ)ᶜ) ∧
      (∀ x, x ∉ boundary σ → ∃ R, x ∈ O R) ∧
      (∀ R, ∀ x ∈ O R, w R x = pFun Λ σ c x / 2) := by
  first | exact @GlobalTheory.PoincareTrunc.smoothTrunc | exact GlobalTheory.PoincareTrunc.smoothTrunc | (intros; apply GlobalTheory.PoincareTrunc.smoothTrunc <;> assumption)

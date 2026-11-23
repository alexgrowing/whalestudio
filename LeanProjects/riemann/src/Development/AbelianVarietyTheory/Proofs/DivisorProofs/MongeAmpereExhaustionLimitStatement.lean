import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereExhaustionLimit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_exhaustion_limit : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (n : ℕ) (Y : Type)
    [TopologicalSpace Y] (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (P : LocPot X)
    (Ψ : ℕ → LocPot X) (O : ℕ → Set X) (a : ℕ → ℝ) (G : Set Y) (g : Y → ℝ≥0∞) (C : ℝ≥0∞),
    (∀ R, IsPotential A (Ψ R)) → (∀ R, IsOpen (O R)) → Monotone O →
    (∀ R x, ∀ y ∈ O R, (Ψ R).φ x y = P.φ x y + a R) → (∀ y ∈ G, ∃ R, μ y ∈ O R) →
    (∀ [MeasurableSpace Y] [BorelSpace Y], Measurable g) → C < ∞ →
    (∀ R, chartSumInt B ((Ψ R).pullback μ hμ.1) Set.univ g ≤ C) →
    chartSumInt B (P.pullback μ hμ.1) G g < ∞ := by
  first | exact @GlobalTheory.chartSumInt_lt_top_of_monotone_limit | exact GlobalTheory.chartSumInt_lt_top_of_monotone_limit | (intros; apply GlobalTheory.chartSumInt_lt_top_of_monotone_limit <;> assumption)

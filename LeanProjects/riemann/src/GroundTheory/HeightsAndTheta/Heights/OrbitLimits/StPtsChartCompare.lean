import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSegreChart
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def PtsChartCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (e : ℕ) (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
    Measurable ({z : (Σ k, ι k) → ℂ | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}.indicator g) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
      Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) g y w|) →
      Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) g y w) →
      ptsIntegralAt P Ψ (pot L) g =
        ∑ᶠ J ∈ (PtsSegreChart.ideal P i).minimalPrimes,
          varInt J e
            ({x | ∀ k, ∃ j, PtsSegreChart.pt x ⟨k, j⟩ ≠ 0}.indicator fun x => g (PtsSegreChart.pt x))
            (PtsSegreChart.chartPot L)

end GroundTheory.Heights₂.Heights

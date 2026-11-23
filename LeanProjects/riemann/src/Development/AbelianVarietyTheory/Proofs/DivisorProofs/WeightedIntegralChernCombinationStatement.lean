import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralChernCombination
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarComplexPointsCompactStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_integral_chern_combination : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (g : CxPts p σ → ℝ) (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
    (∀ n ∈ s, ∀ ε : ℤˣ, Integrable g ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε)) →
    wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) =
      ∑ n ∈ s, c n * wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) := by
  first | exact @GlobalTheory.LineForm.PolarSum.wInt_sum_lin_pow | exact GlobalTheory.LineForm.PolarSum.wInt_sum_lin_pow | (intros; apply GlobalTheory.LineForm.PolarSum.wInt_sum_lin_pow <;> assumption)

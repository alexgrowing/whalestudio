import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntersectionCombinationLogNorm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_intersection_combination_log_norm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (ι : Type) [Fintype ι] (L : ι → HermLB p) (N : HermLB p)
    (r : N.B.ι → X.functionFieldˣ) (hr : IsRatSec N.B r) (g : ∀ σ : k →+* ℂ, CxPts p σ → ℝ),
    (∀ σ, ∀ y ∈ offSupp p σ (N.div hr), logNorm (N.φ σ) r y = g σ y) →
    ∀ (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
      ∑ n ∈ s, c n * (comb L n).archInt N D hr =
        ∑ᶠ σ : k →+* ℂ, wInt (hX.atlas σ) (g σ) (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) := by
  first | exact @GlobalTheory.ChernPoly.archInt_sum_eq_wInt | exact GlobalTheory.ChernPoly.archInt_sum_eq_wInt | (intros; apply GlobalTheory.ChernPoly.archInt_sum_eq_wInt <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcLogPlusConstant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_log_plus_constant : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (f : M → ℝ), A.SmoothOn Set.univ (fun y => (f y : ℂ)) → (∀ y, 0 ≤ f y) →
    ∀ t : ℝ, 0 < t → A.ddc (A.fn (fun y => Real.log (f y + t))) =
      A.fn (fun y => 1 / (f y + t)) * A.ddc (A.fn f) - A.fn (fun y => 1 / (f y + t) ^ 2) * (GlobalTheory.HermFrame.kappa • (A.del (A.fn f) * A.dbar (A.fn f))) := by
  first | exact @GlobalTheory.ChainLog.ddc_fn_log_add | exact GlobalTheory.ChainLog.ddc_fn_log_add | (intros; apply GlobalTheory.ChainLog.ddc_fn_log_add <;> assumption)

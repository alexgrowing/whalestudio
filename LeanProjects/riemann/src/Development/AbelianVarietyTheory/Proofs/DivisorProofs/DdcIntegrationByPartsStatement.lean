import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcIntegrationByParts
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_integration_by_parts : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (g : M → ℝ),
    A.SmoothOn Set.univ (fun y => (g y : ℂ)) → ∀ ψ : A.Fld, A.IsForm ψ → A.integral (A.fn g * A.ddc ψ) = A.integral (A.ddc (A.fn g) * ψ) := by
  first | exact @GlobalTheory.CxForm.ByParts.integral_fn_mul_ddc | exact GlobalTheory.CxForm.ByParts.integral_fn_mul_ddc | (intros; apply GlobalTheory.CxForm.ByParts.integral_fn_mul_ddc <;> assumption)

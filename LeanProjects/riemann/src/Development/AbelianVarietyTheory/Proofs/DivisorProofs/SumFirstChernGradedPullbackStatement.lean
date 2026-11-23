import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFirstChernGradedPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_first_chern_graded_pullback : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    c1F hY σ (VMetric.grLB fl' 0 (H.pull π w)) + c1F hY σ (VMetric.grLB fl' 1 (H.pull π w)) = c1F hY σ ((VMetric.grLB fl 0 H).pull π w) + c1F hY σ ((VMetric.grLB fl 1 H).pull π w) := by
  first | exact @GlobalTheory.LineForm.c1F_grLB_sum_pullback_eq_pullback_sum | exact GlobalTheory.LineForm.c1F_grLB_sum_pullback_eq_pullback_sum | (intros; apply GlobalTheory.LineForm.c1F_grLB_sum_pullback_eq_pullback_sum <;> assumption)

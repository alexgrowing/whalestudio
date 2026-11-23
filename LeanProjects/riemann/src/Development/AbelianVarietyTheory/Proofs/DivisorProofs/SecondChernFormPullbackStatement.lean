import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernFormPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_chern_form_pullback : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    fld _ (c2F hY σ (h.pull π w) fl') = pullF hX hY σ π w (fld _ (c2F hX σ h fl)) := by
  first | exact @GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F | exact GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F | (intros; apply GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormProperties
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChern_form_properties : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    (∀ L M : HermLB p, (hX.atlas σ).IsRealForm 1 (fld _ (c1F hX σ L)) ∧ (hX.atlas σ).del (fld _ (c1F hX σ L)) = 0 ∧
      (hX.atlas σ).dbar (fld _ (c1F hX σ L)) = 0 ∧ c1F hX σ (L.tens M) = c1F hX σ L + c1F hX σ M ∧ c1F hX σ L.dual = -c1F hX σ L ∧
      (L.Isometric M → c1F hX σ L = c1F hX σ M)) ∧
    (∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2),
      (hX.atlas σ).IsRealForm 1 (fld _ (omF hX σ h fl)) ∧ (hX.atlas σ).IsRealForm 2 (fld _ (c2F hX σ h fl)) ∧
      (hX.atlas σ).del (fld _ (c2F hX σ h fl)) = 0 ∧ (hX.atlas σ).dbar (fld _ (c2F hX σ h fl)) = 0 ∧
      c2F hX σ h fl = c2F hX σ h fl' ∧ omF hX σ h fl * omF hX σ h fl = 0 ∧
      c1F hX σ (VMetric.grLB fl 0 H) + c1F hX σ (VMetric.grLB fl 1 H) = c1F hX σ (VMetric.grLB fl' 0 H) + c1F hX σ (VMetric.grLB fl' 1 H) ∧
      (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) =
        fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H))) ∧
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
      (hX.atlas σ).IsHolo (hY.atlas σ) (GlobalTheory.Points.PtsOver.map π w _) ∧
      (∀ L : HermLB p, fld _ (c1F hY σ (L.pull π w)) = pullF hX hY σ π w (fld _ (c1F hX σ L))) ∧
      ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
        fld _ (c2F hY σ (h.pull π w) fl') = pullF hX hY σ π w (fld _ (c2F hX σ h fl)) ∧
        c1F hY σ (VMetric.grLB fl' 0 (H.pull π w)) + c1F hY σ (VMetric.grLB fl' 1 (H.pull π w)) =
          c1F hY σ ((VMetric.grLB fl 0 H).pull π w) + c1F hY σ ((VMetric.grLB fl 1 H).pull π w) := by
  first | exact @GlobalTheory.LineForm.basicForms | exact GlobalTheory.LineForm.basicForms | (intros; apply GlobalTheory.LineForm.basicForms <;> assumption)

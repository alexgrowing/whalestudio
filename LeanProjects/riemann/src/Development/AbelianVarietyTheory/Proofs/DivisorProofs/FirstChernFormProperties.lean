import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernTensorAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernDualNegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIsometricEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernRealClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernFlagIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormSqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedFirstChernSumIndepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcOmegaFormEqC2SubC1ProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsMapHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernFormPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFirstChernGradedPullbackStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LineForm

theorem basicForms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
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
  intro k _ X _ p D hX σ
  refine ⟨fun L M => ⟨(GlobalTheory.T.firstChern_real_closed k X p D hX σ L).1, (GlobalTheory.T.firstChern_real_closed k X p D hX σ L).2.1, (GlobalTheory.T.firstChern_real_closed k X p D hX σ L).2.2,
    GlobalTheory.T.firstChern_tensor_add k X p D hX σ L M, GlobalTheory.T.firstChern_dual_neg k X p D hX σ L, GlobalTheory.T.firstChern_isometric_eq k X p D hX σ L M⟩,
    fun E h H fl fl' => ⟨GlobalTheory.T.flag_omega_form_real k X p D hX σ E h H fl, (GlobalTheory.T.secondChern_real_closed k X p D hX σ E h H fl).1, (GlobalTheory.T.secondChern_real_closed k X p D hX σ E h H fl).2.1,
      (GlobalTheory.T.secondChern_real_closed k X p D hX σ E h H fl).2.2, GlobalTheory.T.secondChern_flag_independent k X p D hX σ E h H fl fl', GlobalTheory.T.flag_omega_form_sq_zero k X p D hX σ E h H fl,
      GlobalTheory.T.graded_first_chern_sum_indep k X p D hX σ E h H fl fl', GlobalTheory.T.ddc_omega_form_eq_c2_sub_c1_product k X p D hX σ E h H fl⟩,
    fun Y p' D' hY π w => ⟨GlobalTheory.T.points_map_holomorphic k X p D hX σ Y p' D' hY π w, GlobalTheory.T.first_chern_form_pullback k X p D hX σ Y p' D' hY π w,
      fun E h H fl fl' => ⟨GlobalTheory.T.second_chern_form_pullback k X p D hX σ Y p' D' hY π w E h H fl fl', GlobalTheory.T.sum_first_chern_graded_pullback k X p D hX σ Y p' D' hY π w E h H fl fl'⟩⟩⟩

end GlobalTheory.LineForm

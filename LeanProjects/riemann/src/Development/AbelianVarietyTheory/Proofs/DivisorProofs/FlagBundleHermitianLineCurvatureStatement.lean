import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineCurvature
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_curvature : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) ∧ (hY.atlas σ).ddc (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) = evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * (X 3 - X 0)) := by
  first | exact @GlobalTheory.LineForm.ddc_omF_sub_pull | exact GlobalTheory.LineForm.ddc_omF_sub_pull | (intros; apply GlobalTheory.LineForm.ddc_omF_sub_pull <;> assumption)

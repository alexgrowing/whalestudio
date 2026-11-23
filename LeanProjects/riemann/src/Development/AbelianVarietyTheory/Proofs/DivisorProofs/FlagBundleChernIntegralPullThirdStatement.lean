import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThird
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_integral_pull_third : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ m : ℕ,
      (hY.atlas σ).integral ((fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) ^ m * pullF hB hY σ π w φ) = 0 ∧
      (hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * (fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) ^ m * pullF hB hY σ π w φ) =
        1 / (m + 1 : ℝ) * (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3] (hs m)) * φ) := by
  first | exact @GlobalTheory.FibGlob.integral_fibre | exact GlobalTheory.FibGlob.integral_fibre | (intros; apply GlobalTheory.FibGlob.integral_fibre <;> assumption)

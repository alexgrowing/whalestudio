import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLinePullbackFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineIntegralFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineDegreeIdentityStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.FibLog

theorem integrableOn_log_one_sub : IntegrableOn (fun t : ℝ => Real.log (1 - t) / 2) (Set.Icc 0 1) := by
  have h1 : IntervalIntegrable (fun t : ℝ => Real.log (1 - t)) volume 0 1 := by
    have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).comp_sub_left 1
    simpa using this.symm
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 h1).div_const 2

theorem integral_log_one_sub : ∫ t in Set.Icc (0 : ℝ) 1, Real.log (1 - t) / 2 = -1 / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_div]
  have : ∫ t in (0 : ℝ)..1, Real.log (1 - t) = ∫ t in (0 : ℝ)..1, Real.log t := by
    rw [intervalIntegral.integral_comp_sub_left (fun t => Real.log t) 1]; simp
  rw [this, integral_log]; norm_num

theorem wInt_log_one_sub : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    (∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ, Integrable (fun y => Real.log (1 - v y) / 2) ((hY.atlas σ).part α ε)) ∧
      ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ →
        wInt (hY.atlas σ) (fun y => Real.log (1 - v y) / 2) (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) = 1 / 2 * (hB.atlas σ).integral φ := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv
  have hm : Measurable v := GlobalTheory.T.flag_bundle_hermitian_line_pullback_form k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hG : Measurable (fun t : ℝ => Real.log (1 - t) / 2) :=
    ((Real.measurable_log.comp (measurable_const.sub measurable_id))).div_const 2
  have key : ∀ (μ : Measure (CxPts p σ)) (C : ENNReal), Measure.map v μ = C • volume.restrict (Set.Icc (0 : ℝ) 1) →
      ∫ y, Real.log (1 - v y) / 2 ∂μ = C.toReal * (-1 / 2) := by
    intro μ C hμ
    have := integral_map (μ := μ) hm.aemeasurable (f := fun t : ℝ => Real.log (1 - t) / 2) hG.aestronglyMeasurable
    rw [← this, hμ, integral_smul_measure, GlobalTheory.FibLog.integral_log_one_sub, smul_eq_mul]
  refine ⟨fun α hα ε => ?_, fun φ hφ => ?_⟩
  · obtain ⟨C, hC, hle⟩ := GlobalTheory.T.flag_bundle_hermitian_line_degree_identity k B Y q p d hB hY π w E h H flB fl hfl A σ v hv α hα ε
    have hi : Integrable (fun t : ℝ => Real.log (1 - t) / 2) (Measure.map v ((hY.atlas σ).part α ε)) :=
      (GlobalTheory.FibLog.integrableOn_log_one_sub.smul_measure hC).mono_measure hle
    exact (integrable_map_measure hG.aestronglyMeasurable hm.aemeasurable).1 hi
  · have h1 := key _ _ (GlobalTheory.T.flag_bundle_hermitian_line_integral_formula k B Y q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ 1)
    have h2 := key _ _ (GlobalTheory.T.flag_bundle_hermitian_line_integral_formula k B Y q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ (-1))
    rw [wInt, h1, h2, HolAtlas.integral, neg_neg, Measure.real, Measure.real]
    ring

end GlobalTheory.FibLog

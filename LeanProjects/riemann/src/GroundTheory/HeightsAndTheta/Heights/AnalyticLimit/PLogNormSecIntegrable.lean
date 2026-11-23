import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLogNormSecIntegrable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeN
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection MIntegrable logNormSec locDens
  locDensCont)

theorem abs_log_mul_exp_le {a : ℝ} (t : ℝ) (ha : 0 ≤ a) :
    |Real.log (a * Real.exp t)| ≤ |Real.log a| + |t| := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_mul h.ne' (Real.exp_pos t).ne', Real.log_exp]; exact abs_add_le _ _

theorem LogNormSecIntegrable.proof : LogNormSecIntegrable.Statement := by
  intro D X _ A L s hL hs _ Φ hΦ j K hK hKc
  refine LocallyIntegrableOn.integrableOn_compact_subset ?_ hK hKc
  intro u0 hu0
  set c := A.chart j with hc
  set p := c.symm u0
  set V := c.target ∩ c.symm ⁻¹' L.U p with hVdef
  have hV : IsOpen V := c.isOpen_inter_preimage_symm (L.isOpen_U p)
  have hu0V : u0 ∈ V := ⟨hu0, L.mem_U p⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0V
  set B := Metric.closedBall u0 (r / 2) with hBdef
  have hBV : B ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  set f : (Fin D → ℂ) → ℂ := s p ∘ c.symm with hfdef
  have hf : AnalyticOnNhd ℂ f V := hs.1 p j
  set φ : (Fin D → ℂ) → ℝ := L.φ p ∘ c.symm with hφdef
  have hφc : ContinuousOn φ V := (hL.1 p j).continuousOn
  have hF : ∀ u ∈ V, logNormSec L s (c.symm u) = Real.log (‖f u‖ * Real.exp (-φ u)) := fun u hu =>
    congrArg Real.log (hs.2 _ p _ ⟨L.mem_U _, hu.2⟩)
  have hDc : ContinuousOn (locDens A Φ j) B :=
    (locDensCont A Φ hΦ j).mono (hBV.trans Set.inter_subset_left)
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hDc
  have hlogf : IntegrableOn (fun u => Real.log ‖f u‖) B :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt' D V f hV hf).integrableOn_compact_subset hBV hBc
  have hφi : IntegrableOn φ B := (hφc.mono hBV).integrableOn_compact hBc
  have hfc : ContinuousOn f B := fun u hu => (hf u (hBV hu)).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun u => Real.log (‖f u‖ * Real.exp (-φ u)) *
      locDens A Φ j u) (volume.restrict B) := by
    have h1 : AEStronglyMeasurable (fun u => ‖f u‖ * Real.exp (-φ u)) (volume.restrict B) :=
      (hfc.norm.mul (Real.continuous_exp.comp_continuousOn (hφc.mono hBV).neg)).aestronglyMeasurable
        hBm
    exact (Real.measurable_log.comp_aemeasurable h1.aemeasurable).aestronglyMeasurable.mul
      (hDc.aestronglyMeasurable hBm)
  have hint : IntegrableOn (fun u => Real.log (‖f u‖ * Real.exp (-φ u)) * locDens A Φ j u) B := by
    refine Integrable.mono' ((hlogf.norm.add hφi.norm).mul_const M) hmeas ?_
    refine ae_restrict_of_forall_mem hBm fun u hu => ?_
    rw [norm_mul]
    have hb := abs_log_mul_exp_le (-φ u) (norm_nonneg (f u))
    rw [abs_neg] at hb
    simp only [Real.norm_eq_abs] at hb ⊢
    exact mul_le_mul hb (hM u hu) (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine hint.congr_fun (fun u hu => ?_) hBm
  simp only
  rw [hF u (hBV hu)]

end GroundTheory.Heights₂.Heights.AnalyticLimit

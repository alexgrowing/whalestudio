import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeAnalytic
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem brIntegrable_of (hLA : LogAbsLocIntStatement) (R : AnRes P J e)
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  intro j K hK hKc
  refine LocallyIntegrableOn.integrableOn_compact_subset ?_ hK hKc
  intro u0 hu0
  obtain ⟨a, ha, hsa, -⟩ := hs
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hu0V : u0 ∈ V := ⟨hu0, R.mem_U x0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0V
  set B := Metric.closedBall u0 (r / 2) with hBdef
  have hBV : B ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun u => R.lift x0 ((R.A.chart j).symm u) with hγdef
  have hγ : ∀ u ∈ V, AnalyticAt ℂ γ u := fun u hu => analyticAt_lift_chart R x0 j hu
  set f : (Fin e → ℂ) → ℂ := fun u => eval (γ u) (map (Int.castRingHom ℂ) s) with hfdef
  have hf : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_eval_poly _ fun p => analyticAt_pi_iff.mp (hγ u hu) p
  set H : (Fin e → ℂ) → ℝ := fun u => A.h (γ u) with hHdef
  have hblk : ∀ u ∈ V, ∀ k, ∃ i, γ u ⟨k, i⟩ ≠ 0 := fun u hu => (R.mem x0 _ hu.2).1
  have hHc : ContinuousOn H V := fun u hu =>
    ((hA.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds (hblk u hu))).comp
      (hγ u hu).continuousAt).continuousWithinAt
  have hHpos : ∀ u ∈ V, 0 < H u := fun u hu => A.pos _ (hblk u hu)
  have hF : ∀ u ∈ V, logNorm A s (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u)) =
      Real.log (‖f u‖ / H u) := by
    intro u hu
    obtain ⟨c, hc, hzc⟩ := R.compat _ x0 _ ⟨R.mem_U _, hu.2⟩
    rw [hzc]
    exact logNorm_bsmul A ha hsa hc (γ u)
  have hDc : ContinuousOn (locDens R.A (fun i => potOf R (L i)) j) B :=
    (locDensCont R.A _ (fun i => isPotential_potOf R (hL i)) j).mono
      (hBV.trans inter_subset_left)
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hDc
  have hlogf : IntegrableOn (fun u => Real.log ‖f u‖) B :=
    (hLA e V f hV hf).integrableOn_compact_subset hBV hBc
  have hlogH : IntegrableOn (fun u => Real.log (H u)) B :=
    ((hHc.mono hBV).log fun u hu => (hHpos u (hBV hu)).ne').integrableOn_compact hBc
  have hfc : ContinuousOn f B := fun u hu => (hf u (hBV hu)).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun u => Real.log (‖f u‖ / H u) *
      locDens R.A (fun i => potOf R (L i)) j u) (volume.restrict B) := by
    have h1 : AEStronglyMeasurable (fun u => ‖f u‖ / H u) (volume.restrict B) :=
      (hfc.norm.div (hHc.mono hBV) fun u hu => (hHpos u (hBV hu)).ne').aestronglyMeasurable hBm
    exact (Real.measurable_log.comp_aemeasurable h1.aemeasurable).aestronglyMeasurable.mul
      (hDc.aestronglyMeasurable hBm)
  have hint : IntegrableOn (fun u => Real.log (‖f u‖ / H u) *
      locDens R.A (fun i => potOf R (L i)) j u) B := by
    refine Integrable.mono' ((hlogf.norm.add hlogH.norm).mul_const M) hmeas ?_
    refine ae_restrict_of_forall_mem hBm fun u hu => ?_
    rw [norm_mul]
    have hb := abs_log_div_le (norm_nonneg (f u)) (hHpos u (hBV hu))
    simp only [Real.norm_eq_abs] at hb ⊢
    exact mul_le_mul hb (hM u hu) (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine hint.congr_fun (fun u hu => ?_) hBm
  simp only
  rw [hF u (hBV hu)]

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

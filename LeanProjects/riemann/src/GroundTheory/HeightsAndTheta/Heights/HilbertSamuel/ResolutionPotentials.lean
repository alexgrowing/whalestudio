import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionMetricObjects
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem resLift_continuousOn (d : HSMDatum D Ω κ) (x : d.R.X) (p : Ix κ) :
    ContinuousOn (fun z => d.R.lift x z p) (d.R.U x) := by
  intro z hz
  obtain ⟨j, hj⟩ := d.R.A.cover z
  have hzt : d.R.A.chart j z ∈ (d.R.A.chart j).target := (d.R.A.chart j).map_source hj
  have hc : ContinuousAt ((fun z => d.R.lift x z p) ∘ (d.R.A.chart j).symm) (d.R.A.chart j z) :=
    (d.R.holo x p j _ ⟨hzt, by rwa [Set.mem_preimage, (d.R.A.chart j).left_inv hj]⟩).continuousAt
  have h := ((d.R.A.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := fun z => d.R.lift x z p) (x := z) (by simpa using hj)).mpr (by simpa using hc)
  exact h.continuousWithinAt

theorem resLift_contDiffOn (d : HSMDatum D Ω κ) (x : d.R.X) (j : Fin d.R.A.n) :
    ContDiffOn ℝ ∞ (fun y => d.R.lift x ((d.R.A.chart j).symm y))
      ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x) :=
  contDiffOn_pi.mpr fun p => ((d.R.holo x p j).contDiffOn_of_completeSpace).restrict_scalars ℝ

theorem resPot_smoothOn (d : HSMDatum D Ω κ) {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m)
    (x : d.R.X) : d.R.A.SmoothOn ((resPot d m).U x) ((resPot d m).φ x) := fun j => by
  have hne : ∀ y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x,
      d.R.lift x ((d.R.A.chart j).symm y) ∈ {z : Ix κ → ℂ | z ≠ 0} :=
    fun y hy => gaamix_ne_zero_of_mcPts (d.R.mem x _ hy.2)
  exact (hm.comp (resLift_contDiffOn d x j) hne).log fun y hy => (m.pos _ (hne y hy)).ne'

theorem isPotential_resPot (d : HSMDatum D Ω κ) {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsPotential d.R.A (resPot d m) := by
  refine ⟨resPot_smoothOn d hm, fun x x' y hy => ?_⟩
  have hy' : y ∈ d.R.U x ∩ d.R.U x' := hy
  obtain ⟨p, hp⟩ := (d.R.mem x' y hy'.2).1 ()
  obtain ⟨c, hc, hcy⟩ := d.R.compat x x' y hy'
  have hnum : d.R.lift x y ⟨(), p⟩ ≠ 0 := by
    rw [hcy]
    exact mul_ne_zero (hc ()) hp
  set r : ℂ := d.R.lift x y ⟨(), p⟩ / d.R.lift x' y ⟨(), p⟩ with hr_def
  have hr : r ≠ 0 := div_ne_zero hnum hp
  have hO : IsOpen (d.R.U x ∩ d.R.U x') := (d.R.isOpen_U x).inter (d.R.isOpen_U x')
  let q : d.R.X → ℂ := fun z => d.R.lift x z ⟨(), p⟩ / d.R.lift x' z ⟨(), p⟩ / r
  let W : Set d.R.X :=
    {z | z ∈ d.R.U x ∩ d.R.U x' ∧ d.R.lift x' z ⟨(), p⟩ ≠ 0 ∧ q z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ContinuousAt (fun z => d.R.lift x z ⟨(), p⟩) z :=
      ((resLift_continuousOn d x _).mono Set.inter_subset_left).continuousAt (hO.mem_nhds hz.1)
    have hd : ContinuousAt (fun z => d.R.lift x' z ⟨(), p⟩) z :=
      ((resLift_continuousOn d x' _).mono Set.inter_subset_right).continuousAt (hO.mem_nhds hz.1)
    filter_upwards [hO.mem_nhds hz.1, hd.eventually_ne hz.2.1,
      ((hn.div hd hz.2.1).div_const r).eventually_mem (Complex.isOpen_slitPlane.mem_nhds hz.2.2)]
      with w h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hyW : y ∈ W := by
    refine ⟨hy', hp, ?_⟩
    have h1 : q y = 1 := div_self hr
    rw [h1]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
  let G : d.R.X → ℂ := fun z => Complex.log (q z) + ((Real.log ‖r‖ : ℝ) : ℂ)
  refine ⟨W, hW, hyW, G, fun j y' hy'' => ?_, fun z hz => ?_⟩
  · have hz : (d.R.A.chart j).symm y' ∈ W := hy''.2
    have hn : AnalyticAt ℂ (fun y'' => d.R.lift x ((d.R.A.chart j).symm y'') ⟨(), p⟩) y' :=
      d.R.holo x _ j y' ⟨hy''.1, hz.1.1⟩
    have hd : AnalyticAt ℂ (fun y'' => d.R.lift x' ((d.R.A.chart j).symm y'') ⟨(), p⟩) y' :=
      d.R.holo x' _ j y' ⟨hy''.1, hz.1.2⟩
    have hq : AnalyticAt ℂ (fun y'' => q ((d.R.A.chart j).symm y'')) y' :=
      (hn.div hd hz.2.1).div analyticAt_const hr
    have hl : AnalyticAt ℂ (Complex.log ∘ fun y'' => q ((d.R.A.chart j).symm y'')) y' :=
      AnalyticAt.comp (f := fun y'' => q ((d.R.A.chart j).symm y'')) (analyticAt_clog hz.2.2) hq
    exact hl.add analyticAt_const
  · have hzW : z ∈ W := hz.1.1
    obtain ⟨c', hc', hcz⟩ := d.R.compat x x' z hzW.1
    have hpos : 0 < m.ρ (d.R.lift x' z) := m.pos _ (gaamix_ne_zero_of_mcPts (d.R.mem x' z hzW.1.2))
    have hsm : d.R.lift x z = c' () • d.R.lift x' z := by
      rw [hcz]
      funext w
      rfl
    have hqz : q z = c' () / r := by
      show d.R.lift x z ⟨(), p⟩ / d.R.lift x' z ⟨(), p⟩ / r = _
      rw [hsm, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hzW.2.1, mul_one]
    show Real.log (m.ρ (d.R.lift x z)) - Real.log (m.ρ (d.R.lift x' z)) = (G z).re
    rw [hsm, m.smul, Real.log_mul (norm_ne_zero_iff.mpr (hc' ())) hpos.ne', add_sub_cancel_right]
    show Real.log ‖c' ()‖ = (Complex.log (q z) + ((Real.log ‖r‖ : ℝ) : ℂ)).re
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, hqz, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr (hc' ())) (norm_ne_zero_iff.mpr hr)]
    ring

theorem continuous_logRatio_resPt (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (h₀ : IsSmoothMetric m₀) (h₁ : IsSmoothMetric m₁) :
    Continuous fun y => logRatio m₀ m₁ (resPt d y) := by
  refine continuous_iff_continuousAt.2 fun y0 => ?_
  have hU : d.R.U y0 ∈ 𝓝 y0 := (d.R.isOpen_U y0).mem_nhds (d.R.mem_U y0)
  have hL : ContinuousOn (d.R.lift y0) (d.R.U y0) :=
    continuousOn_pi.2 fun p => resLift_continuousOn d y0 p
  have hlog : ContinuousOn (fun y => logRatio m₀ m₁ (d.R.lift y0 y)) (d.R.U y0) :=
    (gbamix_smooth_logRatio h₀ h₁).continuousOn.comp hL
      fun y hy => gaamix_ne_zero_of_mcPts (d.R.mem y0 y hy)
  have heq : (fun y => logRatio m₀ m₁ (d.R.lift y0 y)) =ᶠ[𝓝 y0]
      fun y => logRatio m₀ m₁ (resPt d y) := by
    filter_upwards [hU] with y hy
    obtain ⟨c, hc, hcy⟩ := d.R.compat y y0 y ⟨d.R.mem_U y, hy⟩
    show _ = logRatio m₀ m₁ (d.R.lift y y)
    rw [hcy, gbamix_logRatio_deg c _ hc]
  exact (hlog.continuousAt hU).congr heq

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

import Mathlib
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

open scoped ContDiff Topology Interval
open Filter Metric Set

namespace GlobalTheory.CoordDivision

noncomputable def seg {e : ℕ} (k : Fin e) (t : ℝ) (z : Fin e → ℂ) : Fin e → ℂ :=
  z + (((t : ℂ) - 1) * z k) • Pi.single k 1

theorem seg_apply {e : ℕ} (k : Fin e) (t : ℝ) (z : Fin e → ℂ) (i : Fin e) :
    seg k t z i = if i = k then (t : ℂ) * z k else z i := by
  by_cases hi : i = k
  · subst hi; simp [seg]; ring
  · simp [seg, hi, Pi.single_apply]

theorem seg_mem_ball {e : ℕ} {k : Fin e} {z0 z : Fin e → ℂ} {r : ℝ} (hr : 0 < r) (hz0 : z0 k = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hz : z ∈ ball z0 r) : seg k t z ∈ ball z0 r := by
  rw [mem_ball, dist_pi_lt_iff hr] at hz ⊢
  intro i
  rw [seg_apply]
  split_ifs with hi
  · subst hi
    have h1 := hz i
    rw [hz0, dist_zero_right] at h1 ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖z i‖ ≤ 1 * ‖z i‖ := by gcongr; exact ht.2
      _ < r := by simpa using h1
  · exact hz i

theorem seg_one {e : ℕ} (k : Fin e) (z : Fin e → ℂ) : seg k 1 z = z := by simp [seg]

theorem seg_zero_apply {e : ℕ} (k : Fin e) (z : Fin e → ℂ) : seg k 0 z k = 0 := by
  simp [seg_apply]

theorem seg_of_eq_zero {e : ℕ} (k : Fin e) (t : ℝ) {z : Fin e → ℂ} (hz : z k = 0) : seg k t z = z := by
  simp [seg, hz]

theorem hadamard_coord {e : ℕ} (h : (Fin e → ℂ) → ℂ) (z0 : Fin e → ℂ) (r : ℝ) (k : Fin e) :
    0 < r → z0 k = 0 → AnalyticOnNhd ℂ h (Metric.ball z0 r) →
    (∀ z ∈ Metric.ball z0 r, z k = 0 → h z = 0) →
    ∃ g : (Fin e → ℂ) → ℂ, ContDiffOn ℝ ∞ g (Metric.ball z0 r) ∧
      g z0 = fderiv ℂ h z0 (Pi.single k 1) ∧ ∀ z ∈ Metric.ball z0 r, h z = z k * g z := by
  intro hr hz0 hh hzero
  set U := ball z0 r with hU_def
  have hU : IsOpen U := isOpen_ball
  set φ : (Fin e → ℂ) → ℂ := fun w => fderiv ℂ h w (Pi.single k 1) with hφ_def
  have hφa : AnalyticOnNhd ℂ φ U := by
    intro w hw
    have hA : AnalyticAt ℂ (fderiv ℂ h) w := hh.fderiv w hw
    exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single k 1 : Fin e → ℂ)).analyticAt _).comp hA
  have hφc : ContinuousOn φ U := hφa.continuousOn
  have hφd : DifferentiableOn ℂ φ U := hφa.differentiableOn
  have hsegc : Continuous (Function.uncurry (seg k)) := by
    unfold Function.uncurry seg; fun_prop
  have hsegd : ∀ t : ℝ, Differentiable ℂ (seg k t) := by
    intro t; unfold seg; fun_prop
  have hmaps : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ U, seg k t z ∈ U := fun t ht z hz =>
    seg_mem_ball hr hz0 ht hz
  have huIcc : [[(0 : ℝ), 1]] = Icc 0 1 := uIcc_of_le zero_le_one
  have hI := differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun t z => φ (seg k t z)) hU (a := 0) (b := 1)
    (by
      refine hφc.comp hsegc.continuousOn ?_
      rintro ⟨t, z⟩ ⟨ht, hz⟩
      exact hmaps t (huIcc ▸ ht) z hz)
    (fun t ht => hφd.comp (hsegd t).differentiableOn fun z hz => hmaps t (huIcc ▸ ht) z hz)
  set g : (Fin e → ℂ) → ℂ := fun z => ∫ t in (0 : ℝ)..1, φ (seg k t z) with hg_def
  refine ⟨g, ?_, ?_, ?_⟩
  · have ha : AnalyticOnNhd ℂ g U := ReciprocityTheory.AnForm.Osgood.osgood e U g hU hI.1
    exact (ha.contDiffOn (n := ∞) hU.uniqueDiffOn).restrict_scalars ℝ
  · simp only [hg_def, seg_of_eq_zero k _ hz0]
    simp [hφ_def]
  · intro z hz
    have hderiv : ∀ t ∈ [[(0 : ℝ), 1]], HasDerivAt (fun s : ℝ => h (seg k s z))
        (z k * φ (seg k t z)) t := by
      intro t ht
      have hw : seg k t z ∈ U := hmaps t (huIcc ▸ ht) z hz
      have hf : HasFDerivAt h (fderiv ℂ h (seg k t z)) (seg k t z) :=
        ((hh _ hw).differentiableAt).hasFDerivAt
      have hγ : HasDerivAt (fun s : ℝ => seg k s z) (z k • (Pi.single k 1 : Fin e → ℂ)) t := by
        have h1 : HasDerivAt (fun s : ℝ => (((s : ℂ) - 1) * z k)) (z k) t := by
          have := ((Complex.ofRealCLM.hasDerivAt (x := t)).sub_const (1 : ℂ)).mul_const (z k)
          simpa using this
        have h2 := (h1.smul_const (Pi.single k 1 : Fin e → ℂ)).const_add z
        simpa [seg] using h2
      have := (hf.restrictScalars ℝ).comp_hasDerivAt t hγ
      have e1 : fderiv ℂ h (seg k t z) (z k • (Pi.single k 1 : Fin e → ℂ)) = z k * φ (seg k t z) := by
        simp [hφ_def, map_smul]
      rw [← e1]
      exact this
    have hcont : ContinuousOn (fun t => z k * φ (seg k t z)) [[(0 : ℝ), 1]] := by
      refine continuousOn_const.mul (hφc.comp (hsegc.comp (Continuous.prodMk_left z)).continuousOn ?_)
      intro t ht
      exact hmaps t (huIcc ▸ ht) z hz
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable)
    rw [intervalIntegral.integral_const_mul, seg_one,
      hzero _ (hmaps 0 ⟨le_rfl, zero_le_one⟩ z hz) (seg_zero_apply k z), sub_zero] at hftc
    exact hftc.symm

end GlobalTheory.CoordDivision

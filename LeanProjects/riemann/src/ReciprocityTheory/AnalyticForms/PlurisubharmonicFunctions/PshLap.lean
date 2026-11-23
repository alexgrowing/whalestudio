import Mathlib

open MeasureTheory Metric Set Filter Topology Real

namespace ReciprocityTheory.AnForm.A.PshLap

noncomputable section

variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}

lemma hasDerivAt_circleMap_radius (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => circleMap 0 s θ) (circleMap 0 1 θ) r := by
  have h := ((hasDerivAt_id r).ofReal_comp).mul_const (Complex.exp (θ * Complex.I))
  simpa [circleMap] using h

lemma hasDerivAt_comp_radius {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → F} {φ' : ℂ →L[ℝ] F} (r θ : ℝ) (h : HasFDerivAt φ φ' (circleMap 0 r θ)) :
    HasDerivAt (fun s : ℝ => φ (circleMap 0 s θ)) (φ' (circleMap 0 1 θ)) r :=
  h.comp_hasDerivAt (f := fun s : ℝ => circleMap 0 s θ) r (hasDerivAt_circleMap_radius r θ)

lemma circleMap_eq_smul (r θ : ℝ) : circleMap 0 r θ = r • circleMap 0 1 θ := by
  simp [circleMap, Complex.real_smul]

lemma clm_circleMap (L : ℂ →L[ℝ] ℝ) (r θ : ℝ) :
    L (circleMap 0 r θ) = r * L (circleMap 0 1 θ) := by
  rw [circleMap_eq_smul r θ, map_smul, smul_eq_mul]

lemma circleMap_mem_closedBall {r R θ : ℝ} (h0 : 0 ≤ r) (h : r ≤ R) :
    circleMap 0 r θ ∈ closedBall (0:ℂ) R := by
  simp [abs_of_nonneg h0, h]

lemma radial_ftc (hg : ∀ x ∈ V, HasFDerivAt g (G x) x) (hGc : ContinuousOn G V)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : closedBall (0:ℂ) R ⊆ V) (θ : ℝ) :
    g (circleMap 0 R θ) - g 0 = ∫ r in (0:ℝ)..R, G (circleMap 0 r θ) (circleMap 0 1 θ) := by
  have hmem : ∀ r ∈ uIcc (0:ℝ) R, circleMap 0 r θ ∈ V := fun r hr => by
    rw [uIcc_of_le hR0] at hr
    exact hR (circleMap_mem_closedBall hr.1 hr.2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r => g (circleMap 0 r θ))
    (fun r hr => (hg _ (hmem r hr)).comp_hasDerivAt r (hasDerivAt_circleMap_radius r θ)) ?_
  · have h0 : circleMap 0 0 θ = 0 := by simp [circleMap]
    rw [h, h0]
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.clm_apply ?_ continuousOn_const
    exact hGc.comp (Continuous.continuousOn (by unfold circleMap; fun_prop)) (fun r hr => hmem r hr)

lemma eq_integral_radial_second (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hGc : ContinuousOn G V)
    (hHc : ContinuousOn H V) {R : ℝ} (hR0 : 0 ≤ R) (hR : closedBall (0:ℂ) R ⊆ V) (θ : ℝ) :
    G (circleMap 0 R θ) (circleMap 0 R θ) = ∫ s in (0:ℝ)..R,
      (s * H (circleMap 0 s θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
        G (circleMap 0 s θ) (circleMap 0 1 θ)) := by
  have hmem : ∀ r ∈ uIcc (0:ℝ) R, circleMap 0 r θ ∈ V := fun r hr => by
    rw [uIcc_of_le hR0] at hr
    exact hR (circleMap_mem_closedBall hr.1 hr.2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => G (circleMap 0 r θ) (circleMap 0 r θ))
    (f' := fun s => s * H (circleMap 0 s θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
        G (circleMap 0 s θ) (circleMap 0 1 θ))
    (fun r hr => by
      have h1 := (hasDerivAt_comp_radius r θ (hGd _ (hmem r hr))).clm_apply
        (hasDerivAt_circleMap_radius r θ)
      refine h1.congr_deriv ?_
      rw [clm_circleMap (H (circleMap 0 r θ) (circleMap 0 1 θ)) r θ]) ?_
  · have h0 : circleMap 0 0 θ = 0 := by simp [circleMap]
    rw [h, h0, map_zero, sub_zero]
  · apply ContinuousOn.intervalIntegrable
    have hc : ContinuousOn (fun r : ℝ => circleMap 0 r θ) (uIcc 0 R) :=
      Continuous.continuousOn (by unfold circleMap; fun_prop)
    refine ContinuousOn.add (ContinuousOn.mul continuousOn_id ?_) ?_
    · exact ((hHc.comp hc (fun r hr => hmem r hr)).clm_apply continuousOn_const).clm_apply
        continuousOn_const
    · exact (hGc.comp hc (fun r hr => hmem r hr)).clm_apply continuousOn_const

lemma angular_period (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hGc : ContinuousOn G V)
    (hHc : ContinuousOn H V) {s : ℝ} (hs : closedBall (0:ℂ) |s| ⊆ V) :
    ∫ θ in (0:ℝ)..2*π, G (circleMap 0 s θ) (circleMap 0 1 θ) =
      s * ∫ θ in (0:ℝ)..2*π, H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I)
        (circleMap 0 1 θ * Complex.I) := by
  have hmem : ∀ θ : ℝ, circleMap 0 s θ ∈ V := fun θ => hs (by simp)
  have hc1 : Continuous fun θ => G (circleMap 0 s θ) (circleMap 0 1 θ) :=
    (hGc.comp_continuous (continuous_circleMap 0 s) hmem).clm_apply (continuous_circleMap 0 1)
  have hc2 : Continuous fun θ => H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I)
      (circleMap 0 1 θ * Complex.I) :=
    ((hHc.comp_continuous (continuous_circleMap 0 s) hmem).clm_apply
      ((continuous_circleMap 0 1).mul continuous_const)).clm_apply
      ((continuous_circleMap 0 1).mul continuous_const)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ => G (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I))
    (f' := fun θ => s * H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I)
        (circleMap 0 1 θ * Complex.I) - G (circleMap 0 s θ) (circleMap 0 1 θ))
    (a := 0) (b := 2 * π)
    (fun θ _ => by
      have h1 := ((hGd _ (hmem θ)).comp_hasDerivAt θ (hasDerivAt_circleMap 0 s θ)).clm_apply
        ((hasDerivAt_circleMap 0 1 θ).mul_const Complex.I)
      refine h1.congr_deriv ?_
      simp only [Function.comp_def]
      have e1 : circleMap 0 s θ * Complex.I = s • (circleMap 0 1 θ * Complex.I) := by
        rw [circleMap_eq_smul s θ, smul_mul_assoc]
      have e2 : circleMap 0 1 θ * Complex.I * Complex.I = - circleMap 0 1 θ := by
        rw [mul_assoc, Complex.I_mul_I]; ring
      rw [e1, e2, map_smul, map_neg]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring) (((hc2.const_mul s).sub hc1).intervalIntegrable 0 (2 * π))
  have hp : circleMap 0 s (2 * π) = circleMap 0 s 0 := by
    simpa using periodic_circleMap 0 s 0
  have hp1 : circleMap 0 1 (2 * π) = circleMap 0 1 0 := by
    simpa using periodic_circleMap 0 1 0
  simp only [hp, hp1, sub_self] at h
  rw [intervalIntegral.integral_sub ((hc2.const_mul s).intervalIntegrable _ _)
    (hc1.intervalIntegrable _ _), intervalIntegral.integral_const_mul] at h
  linarith

end

end ReciprocityTheory.AnForm.A.PshLap

open MeasureTheory Metric Set Filter Topology Real

namespace ReciprocityTheory.AnForm.A.PshLap

noncomputable section

lemma swap_cont {F : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc c d)) :
    ∫ x in a..b, ∫ y in c..d, F x y = ∫ y in c..d, ∫ x in a..b, F x y := by
  have hI : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  exact integral_integral_swap hI

lemma intervalIntegrable_param {F : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc c d)) :
    IntervalIntegrable (fun x => ∫ y in c..d, F x y) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hI : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have h := hI.integral_prod_left
  simp only [Function.uncurry_apply_pair] at h
  simp only [intervalIntegral.integral_of_le hcd]
  exact h

lemma continuous_circleMap_uncurry : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
  unfold circleMap; fun_prop

lemma rot_id (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (θ : ℝ) :
    B (circleMap 0 1 θ) (circleMap 0 1 θ) +
      B (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I) = B 1 1 + B Complex.I Complex.I := by
  have h1 : circleMap 0 1 θ = (Real.cos θ) • (1:ℂ) + (Real.sin θ) • Complex.I := by
    apply Complex.ext <;> simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have h2 : circleMap 0 1 θ * Complex.I = (-Real.sin θ) • (1:ℂ) + (Real.cos θ) • Complex.I := by
    apply Complex.ext <;> simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  rw [h2, h1]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  linear_combination (B 1 1 + B Complex.I Complex.I) * Real.sin_sq_add_cos_sq θ

variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}

def Pr (G : ℂ → ℂ →L[ℝ] ℝ) (r : ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..2*π, G (circleMap 0 r θ) (circleMap 0 1 θ)

def Lap (H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (s : ℝ) : ℝ :=
  ∫ θ in (0:ℝ)..2*π, (H (circleMap 0 s θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
    H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I))

lemma mapsTo_rect {R a : ℝ} (hR : closedBall (0:ℂ) R ⊆ V) :
    MapsTo (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) (Icc 0 R ×ˢ Icc 0 a) V :=
  fun _ hp => hR (circleMap_mem_closedBall hp.1.1 hp.1.2)

lemma contOn_G (hGc : ContinuousOn G V) {R a : ℝ} (hR : closedBall (0:ℂ) R ⊆ V) :
    ContinuousOn (Function.uncurry fun r θ => G (circleMap 0 r θ) (circleMap 0 1 θ))
      (Icc 0 R ×ˢ Icc 0 a) :=
  (hGc.comp continuous_circleMap_uncurry.continuousOn (mapsTo_rect hR)).clm_apply
    ((continuous_circleMap 0 1).comp continuous_snd).continuousOn

lemma mean_formula (hg : ∀ x ∈ V, HasFDerivAt g (G x) x) (hGc : ContinuousOn G V) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : closedBall (0:ℂ) R ⊆ V) :
    Real.circleAverage g 0 R - g 0 = (2*π)⁻¹ * ∫ r in (0:ℝ)..R, Pr G r := by
  have hgc : Continuous fun θ => g (circleMap 0 R θ) := by
    have : ContinuousOn g V := fun x hx => (hg x hx).continuousAt.continuousWithinAt
    exact this.comp_continuous (continuous_circleMap 0 R)
      (fun θ => hR (circleMap_mem_closedBall hR0 le_rfl))
  have h1 : ∫ θ in (0:ℝ)..2*π, (g (circleMap 0 R θ) - g 0) =
      ∫ θ in (0:ℝ)..2*π, ∫ r in (0:ℝ)..R, G (circleMap 0 r θ) (circleMap 0 1 θ) :=
    intervalIntegral.integral_congr (fun θ _ => radial_ftc hg hGc hR0 hR θ)
  have h2 : ∫ θ in (0:ℝ)..2*π, (g (circleMap 0 R θ) - g 0) =
      (∫ θ in (0:ℝ)..2*π, g (circleMap 0 R θ)) - 2 * π * g 0 := by
    rw [intervalIntegral.integral_sub (hgc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have h3 := swap_cont (F := fun r θ => G (circleMap 0 r θ) (circleMap 0 1 θ)) hR0
    two_pi_pos.le (contOn_G hGc hR)
  have h4 : (2*π)⁻¹ * (2 * π * g 0) = g 0 := by field_simp
  rw [Real.circleAverage_def, smul_eq_mul]
  unfold Pr
  rw [h3, ← h1, h2, mul_sub, h4]

lemma rP_formula (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hGc : ContinuousOn G V)
    (hHc : ContinuousOn H V) {R r : ℝ} (hr0 : 0 ≤ r) (hrR : r ≤ R)
    (hR : closedBall (0:ℂ) R ⊆ V) :
    r * Pr G r = ∫ s in (0:ℝ)..r, s * Lap H s := by
  have hr : closedBall (0:ℂ) r ⊆ V := (closedBall_subset_closedBall hrR).trans hR
  have hmem : ∀ s ∈ uIcc (0:ℝ) r, ∀ θ : ℝ, circleMap 0 s θ ∈ V := fun s hs θ => by
    rw [uIcc_of_le hr0] at hs
    exact hr (circleMap_mem_closedBall hs.1 hs.2)
  have hcG : ∀ s ∈ uIcc (0:ℝ) r, Continuous fun θ => G (circleMap 0 s θ) (circleMap 0 1 θ) :=
    fun s hs => (hGc.comp_continuous (continuous_circleMap 0 s) (hmem s hs)).clm_apply
      (continuous_circleMap 0 1)
  have hcH : ∀ s ∈ uIcc (0:ℝ) r, ∀ u : ℂ, Continuous fun θ =>
      H (circleMap 0 s θ) (circleMap 0 1 θ * u) (circleMap 0 1 θ * u) :=
    fun s hs u => ((hHc.comp_continuous (continuous_circleMap 0 s) (hmem s hs)).clm_apply
      ((continuous_circleMap 0 1).mul continuous_const)).clm_apply
      ((continuous_circleMap 0 1).mul continuous_const)
  have e1 : r * Pr G r = ∫ θ in (0:ℝ)..2*π, G (circleMap 0 r θ) (circleMap 0 r θ) := by
    unfold Pr
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [clm_circleMap (G (circleMap 0 r θ)) r θ]
  have e2 := intervalIntegral.integral_congr (μ := volume) (a := (0:ℝ)) (b := 2*π)
    (fun θ (_ : θ ∈ uIcc (0:ℝ) (2*π)) => eq_integral_radial_second hGd hGc hHc hr0 hr θ)
  have hcont : ContinuousOn (Function.uncurry fun s θ =>
      s * H (circleMap 0 s θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
        G (circleMap 0 s θ) (circleMap 0 1 θ)) (Icc 0 r ×ˢ Icc 0 (2*π)) := by
    refine ContinuousOn.add (ContinuousOn.mul continuous_fst.continuousOn ?_) (contOn_G hGc hr)
    exact ((hHc.comp continuous_circleMap_uncurry.continuousOn (mapsTo_rect hr)).clm_apply
      ((continuous_circleMap 0 1).comp continuous_snd).continuousOn).clm_apply
      ((continuous_circleMap 0 1).comp continuous_snd).continuousOn
  have e3 := swap_cont hr0 two_pi_pos.le hcont
  rw [e1, e2, ← e3]
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  have hs' : closedBall (0:ℂ) |s| ⊆ V := by
    rw [uIcc_of_le hr0] at hs
    rw [abs_of_nonneg hs.1]
    exact (closedBall_subset_closedBall hs.2).trans hr
  have hH1 := hcH s hs 1
  simp only [mul_one] at hH1
  rw [intervalIntegral.integral_add ((hH1.const_mul s).intervalIntegrable _ _)
    ((hcG s hs).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    angular_period hGd hGc hHc hs', Lap, intervalIntegral.integral_add (hH1.intervalIntegrable _ _)
    ((hcH s hs Complex.I).intervalIntegrable _ _)]
  ring

end

end ReciprocityTheory.AnForm.A.PshLap

open MeasureTheory Metric Set Filter Topology Real

namespace ReciprocityTheory.AnForm.A.PshLap

noncomputable section

variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}

lemma contOn_H (hHc : ContinuousOn H V) {R a : ℝ} (hR : closedBall (0:ℂ) R ⊆ V) :
    ContinuousOn (Function.uncurry fun s θ =>
      H (circleMap 0 s θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
        H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I))
      (Icc 0 R ×ˢ Icc 0 a) := by
  have hc := hHc.comp continuous_circleMap_uncurry.continuousOn (mapsTo_rect (a := a) hR)
  have he : Continuous fun p : ℝ × ℝ => circleMap 0 1 p.2 :=
    (continuous_circleMap 0 1).comp continuous_snd
  refine ContinuousOn.add ((hc.clm_apply he.continuousOn).clm_apply he.continuousOn) ?_
  exact (hc.clm_apply (he.mul continuous_const).continuousOn).clm_apply
    (he.mul continuous_const).continuousOn

theorem le_circleAverage_of_lap_nonneg (hg : ∀ x ∈ V, HasFDerivAt g (G x) x)
    (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hHc : ContinuousOn H V) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : closedBall (0:ℂ) R ⊆ V)
    (hpos : ∀ x ∈ closedBall (0:ℂ) R, ∀ θ : ℝ, 0 ≤ H x (circleMap 0 1 θ) (circleMap 0 1 θ) +
      H x (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I)) :
    g 0 ≤ Real.circleAverage g 0 R := by
  have hGc : ContinuousOn G V := fun x hx => (hGd x hx).continuousAt.continuousWithinAt
  have hm := mean_formula hg hGc hR0 hR
  have hP : 0 ≤ ∫ r in (0:ℝ)..R, Pr G r := by
    rw [intervalIntegral.integral_of_le hR0]
    refine setIntegral_nonneg measurableSet_Ioc (fun r hr => ?_)
    have h1 := rP_formula hGd hGc hHc hr.1.le hr.2 hR
    have h2 : 0 ≤ ∫ s in (0:ℝ)..r, s * Lap H s := by
      refine intervalIntegral.integral_nonneg hr.1.le (fun s hs => mul_nonneg hs.1 ?_)
      exact intervalIntegral.integral_nonneg two_pi_pos.le
        (fun θ _ => hpos _ (circleMap_mem_closedBall hs.1 (hs.2.trans hr.2)) θ)
    rw [← h1] at h2
    exact (mul_nonneg_iff_of_pos_left hr.1).mp h2
  have : 0 ≤ (2*π)⁻¹ * ∫ r in (0:ℝ)..R, Pr G r := mul_nonneg (by positivity) hP
  linarith

theorem circleAverage_sub_le (hg : ∀ x ∈ V, HasFDerivAt g (G x) x)
    (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hHc : ContinuousOn H V) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : closedBall (0:ℂ) R ⊆ V) (K : ℝ)
    (hK : ∀ x ∈ closedBall (0:ℂ) R, ∀ θ : ℝ, H x (circleMap 0 1 θ) (circleMap 0 1 θ) +
      H x (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I) ≤ K) :
    Real.circleAverage g 0 R - g 0 ≤ K * R ^ 2 / 4 := by
  have hGc : ContinuousOn G V := fun x hx => (hGd x hx).continuousAt.continuousWithinAt
  rw [mean_formula hg hGc hR0 hR]
  have hPint : IntervalIntegrable (Pr G) volume 0 R :=
    intervalIntegrable_param hR0 two_pi_pos.le (contOn_G hGc hR)
  have hb : ∀ r ∈ Ioc (0:ℝ) R, Pr G r ≤ π * K * r := by
    intro r hr
    have hrV : closedBall (0:ℂ) r ⊆ V := (closedBall_subset_closedBall hr.2).trans hR
    have h1 := rP_formula hGd hGc hHc hr.1.le hr.2 hR
    have hLapInt : IntervalIntegrable (Lap H) volume 0 r :=
      intervalIntegrable_param hr.1.le two_pi_pos.le (contOn_H hHc hrV)
    have h2 : ∫ s in (0:ℝ)..r, s * Lap H s ≤ ∫ s in (0:ℝ)..r, s * (2 * π * K) := by
      refine intervalIntegral.integral_mono_on hr.1.le ?_ ?_ (fun s hs => ?_)
      · exact hLapInt.continuousOn_mul continuousOn_id
      · exact (continuous_id.mul continuous_const).intervalIntegrable _ _
      · refine mul_le_mul_of_nonneg_left ?_ hs.1
        have hK' : ∫ θ in (0:ℝ)..2*π, K = 2 * π * K := by simp
        rw [← hK']
        unfold Lap
        have hmem : ∀ θ : ℝ, circleMap 0 s θ ∈ V := fun θ =>
          hrV (circleMap_mem_closedBall hs.1 hs.2)
        have hc := hHc.comp_continuous (continuous_circleMap 0 s) hmem
        have he := continuous_circleMap 0 1
        refine intervalIntegral.integral_mono_on two_pi_pos.le ?_ intervalIntegrable_const
          (fun θ _ => hK _ (circleMap_mem_closedBall hs.1 (hs.2.trans hr.2)) θ)
        exact (((hc.clm_apply he).clm_apply he).add
          ((hc.clm_apply (he.mul continuous_const)).clm_apply
            (he.mul continuous_const))).intervalIntegrable _ _
    have h3 : ∫ s in (0:ℝ)..r, s * (2 * π * K) = π * K * r ^ 2 := by
      rw [intervalIntegral.integral_mul_const, integral_id]; ring
    have h4 : r * Pr G r ≤ r * (π * K * r) := by nlinarith
    exact le_of_mul_le_mul_left h4 hr.1
  have h4 : ∫ r in (0:ℝ)..R, Pr G r ≤ ∫ r in (0:ℝ)..R, π * K * r := by
    rw [intervalIntegral.integral_of_le hR0, intervalIntegral.integral_of_le hR0]
    exact setIntegral_mono_on hPint.1
      ((continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      measurableSet_Ioc hb
  have h5 : ∫ r in (0:ℝ)..R, π * K * r = π * K * R ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rw [h5] at h4
  have h6 : (2*π)⁻¹ * ∫ r in (0:ℝ)..R, Pr G r ≤ (2*π)⁻¹ * (π * K * R ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  calc _ ≤ _ := h6
    _ = K * R ^ 2 / 4 := by field_simp; ring

theorem lap_nonneg_of_sub_mean (hg : ∀ x ∈ V, HasFDerivAt g (G x) x)
    (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hHc : ContinuousOn H V) {R : ℝ} (hR0 : 0 < R)
    (hR : closedBall (0:ℂ) R ⊆ V)
    (hsub : ∀ r ∈ Ioc (0:ℝ) R, g 0 ≤ Real.circleAverage g 0 r) :
    0 ≤ H 0 1 1 + H 0 Complex.I Complex.I := by
  by_contra hc
  push_neg at hc
  set c := H 0 1 1 + H 0 Complex.I Complex.I with hcdef
  have h0V : (0:ℂ) ∈ V := hR (mem_closedBall_self hR0.le)
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp (hHc 0 h0V) (-c/4) (by linarith)
  set ρ := min (δ/2) R with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) hR0
  have hρR : ρ ≤ R := min_le_right _ _
  have hK : ∀ x ∈ closedBall (0:ℂ) ρ, ∀ θ : ℝ, H x (circleMap 0 1 θ) (circleMap 0 1 θ) +
      H x (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I) ≤ c / 2 := by
    intro x hx θ
    have hxV : x ∈ V := hR (closedBall_subset_closedBall hρR hx)
    have hd : dist x 0 < δ :=
      lt_of_le_of_lt (mem_closedBall.mp hx) (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    have hn : ‖H x - H 0‖ < -c/4 := by simpa [dist_eq_norm] using hball hxV hd
    have hrot := rot_id (H 0) θ
    have he : ‖circleMap 0 1 θ‖ = 1 := by simp
    have heI : ‖circleMap 0 1 θ * Complex.I‖ = 1 := by simp
    have b1 : |(H x - H 0) (circleMap 0 1 θ) (circleMap 0 1 θ)| ≤ ‖H x - H 0‖ := by
      have := (H x - H 0).le_opNorm₂ (circleMap 0 1 θ) (circleMap 0 1 θ)
      rw [he] at this; simpa [Real.norm_eq_abs] using this
    have b2 : |(H x - H 0) (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I)| ≤
        ‖H x - H 0‖ := by
      have := (H x - H 0).le_opNorm₂ (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I)
      rw [heI] at this; simpa [Real.norm_eq_abs] using this
    simp only [ContinuousLinearMap.sub_apply] at b1 b2
    have := abs_le.mp b1
    have := abs_le.mp b2
    linarith
  have h1 := circleAverage_sub_le hg hGd hHc hρ.le
    ((closedBall_subset_closedBall hρR).trans hR) (c/2) hK
  have h2 := hsub ρ ⟨hρ, hρR⟩
  have h3 : c / 2 * ρ ^ 2 / 4 < 0 := by
    have : 0 < ρ ^ 2 := by positivity
    nlinarith
  linarith

end

end ReciprocityTheory.AnForm.A.PshLap

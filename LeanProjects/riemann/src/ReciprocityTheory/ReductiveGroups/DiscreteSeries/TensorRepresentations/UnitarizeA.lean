import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.UnitA

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)

def pr (a b : G → ℂ) : ℂ := ∫ x, star (a x) * b x ∂μ

def nrm (a : G → ℂ) : ℝ := (eLpNorm a 2 μ).toReal

variable {μ}

theorem pr_int {a b : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun x => star (a x) * b x) μ := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (ha.toLp a) (hb.toLp b)
  refine h.congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx1 hx2
  rw [hx1, hx2, RCLike.inner_apply, starRingEnd_apply, mul_comm]

theorem pr_eq_inner {a b : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    pr μ a b = inner ℂ (ha.toLp a) (hb.toLp b) := by
  rw [MeasureTheory.L2.inner_def]
  unfold pr
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx1 hx2
  rw [hx1, hx2, RCLike.inner_apply, starRingEnd_apply, mul_comm]

theorem pr_bound {a b : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ‖pr μ a b‖ ≤ nrm μ a * nrm μ b := by
  rw [pr_eq_inner ha hb]
  have h := norm_inner_le_norm (𝕜 := ℂ) (ha.toLp a) (hb.toLp b)
  simpa only [nrm, Lp.norm_toLp] using h

theorem pr_star (a b : G → ℂ) : star (pr μ a b) = pr μ b a := by
  unfold pr
  have h : ∫ x, (starRingEnd ℂ) (star (a x) * b x) ∂μ =
      (starRingEnd ℂ) (∫ x, star (a x) * b x ∂μ) := integral_conj
  simp only [starRingEnd_apply] at h
  rw [← h]
  congr 1
  funext x
  rw [star_mul, star_star]

theorem pr_sub_left {a a₁ b : G → ℂ} (ha : MemLp a 2 μ) (ha₁ : MemLp a₁ 2 μ) (hb : MemLp b 2 μ) :
    pr μ (fun x => a x - a₁ x) b = pr μ a b - pr μ a₁ b := by
  unfold pr
  rw [← integral_sub (pr_int ha hb) (pr_int ha₁ hb)]
  congr 1
  funext x
  rw [star_sub, sub_mul]

theorem pr_neg_right (a b : G → ℂ) : pr μ a (fun x => -b x) = -pr μ a b := by
  unfold pr
  rw [← integral_neg]
  congr 1
  funext x
  rw [mul_neg]

theorem int_norm_le {a b : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ∫ x, ‖star (a x) * b x‖ ∂μ ≤ nrm μ a * nrm μ b := by
  have hA : MemLp (fun x => ‖a x‖) 2 μ := ha.norm
  have hB : MemLp (fun x => ‖b x‖) 2 μ := hb.norm
  have h1 : ∫ x, ‖star (a x) * b x‖ ∂μ = inner ℝ (hA.toLp _) (hB.toLp _) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hA.coeFn_toLp, hB.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply, norm_mul, norm_star]
    simp only [starRingEnd_apply, star_trivial]
    ring
  rw [h1]
  calc inner ℝ (hA.toLp _) (hB.toLp _) ≤ ‖hA.toLp _‖ * ‖hB.toLp _‖ := real_inner_le_norm _ _
    _ = nrm μ a * nrm μ b := by
      simp only [nrm, Lp.norm_toLp, eLpNorm_norm]

theorem pr_add_left {a a₁ b : G → ℂ} (ha : MemLp a 2 μ) (ha₁ : MemLp a₁ 2 μ) (hb : MemLp b 2 μ) :
    pr μ (a + a₁) b = pr μ a b + pr μ a₁ b := by
  unfold pr
  rw [← integral_add (pr_int ha hb) (pr_int ha₁ hb)]
  congr 1
  funext x
  simp only [Pi.add_apply, star_add, add_mul]

theorem pr_add_right {a b b₁ : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (hb₁ : MemLp b₁ 2 μ) :
    pr μ a (b + b₁) = pr μ a b + pr μ a b₁ := by
  unfold pr
  rw [← integral_add (pr_int ha hb) (pr_int ha hb₁)]
  congr 1
  funext x
  simp only [Pi.add_apply, mul_add]

theorem pr_smul_left (c : ℂ) (a b : G → ℂ) : pr μ (c • a) b = star c * pr μ a b := by
  unfold pr
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem pr_smul_right (c : ℂ) (a b : G → ℂ) : pr μ a (c • b) = c * pr μ a b := by
  unfold pr
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem pr_self_re {a : G → ℂ} (ha : MemLp a 2 μ) :
    pr μ a a = ((∫ x, ‖a x‖ ^ 2 ∂μ : ℝ) : ℂ) ∧ Integrable (fun x => ‖a x‖ ^ 2) μ := by
  have hI : Integrable (fun x => ‖a x‖ ^ 2) μ := by
    refine (pr_int ha ha).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, norm_star, sq]
  refine ⟨?_, hI⟩
  unfold pr
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  rw [Complex.ofReal_pow]
  exact Complex.conj_mul' (a x)

section Invariant

variable [μ.IsMulRightInvariant]

theorem memLp_rt {a : G → ℂ} (ha : MemLp a 2 μ) (g : G) : MemLp (fun x => a (x * g)) 2 μ := by
  exact ha.comp_measurePreserving (measurePreserving_mul_right μ g)

theorem nrm_rt {a : G → ℂ} (ha : AEStronglyMeasurable a μ) (g : G) :
    nrm μ (fun x => a (x * g)) = nrm μ a := by
  unfold nrm
  have h := eLpNorm_comp_measurePreserving (p := 2) ha (measurePreserving_mul_right μ g)
  exact congrArg ENNReal.toReal h

theorem pr_rt (a b : G → ℂ) (g : G) :
    pr μ (fun x => a (x * g)) (fun x => b (x * g)) = pr μ a b := by
  unfold pr
  exact integral_mul_right_eq_self (fun x => star (a x) * b x) g

theorem pr_shift (a b : G → ℂ) (g : G) :
    pr μ (fun x => a (x * g)) b = pr μ a (fun x => b (x * g⁻¹)) := by
  rw [← pr_rt (fun x => a (x * g)) b g⁻¹]
  simp only [inv_mul_cancel_right, mul_inv_cancel_right]

end Invariant

theorem ftc {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) {a a' : G → ℂ} (ha' : Continuous a')
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t) (x : G) (t : ℝ) :
    ∫ s in (0:ℝ)..t, a' (x * φ s) = a (x * φ t) - a x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => a (x * φ s))
    (f' := fun s => a' (x * φ s)) (a := 0) (b := t) (fun s _ => hd x s)
    ((ha'.comp (continuous_const.mul hφc)).intervalIntegrable 0 t)
  simpa only [hφ0, mul_one] using h

section Flow

variable [μ.IsMulRightInvariant] [SFinite μ]

theorem incr {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) {a a' b : G → ℂ}
    (ha' : Continuous a') (hb : Continuous b)
    (haL : MemLp a 2 μ) (ha'L : MemLp a' 2 μ) (hbL : MemLp b 2 μ)
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => pr μ (fun x => a' (x * φ s)) b) MeasureTheory.volume 0 t ∧
    pr μ (fun x => a (x * φ t)) b - pr μ a b =
      ∫ s in (0:ℝ)..t, pr μ (fun x => a' (x * φ s)) b := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hFc : Continuous (fun p : ℝ × G => star (a' (p.2 * φ p.1)) * b p.2) :=
    (continuous_star.comp (ha'.comp (continuous_snd.mul (hφc.comp continuous_fst)))).mul
      (hb.comp continuous_snd)
  have hm : AEStronglyMeasurable (fun p : ℝ × G => star (a' (p.2 * φ p.1)) * b p.2)
      ((volume.restrict (Set.Ioc (0:ℝ) t)).prod μ) := hFc.aestronglyMeasurable
  have hFint : Integrable (fun p : ℝ × G => star (a' (p.2 * φ p.1)) * b p.2)
      ((volume.restrict (Set.Ioc (0:ℝ) t)).prod μ) := by
    rw [integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall fun s => pr_int (memLp_rt ha'L (φ s)) hbL, ?_⟩
    refine Integrable.mono' (integrable_const (nrm μ a' * nrm μ b)) hm.norm.integral_prod_right'
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have h := int_norm_le (memLp_rt ha'L (φ s)) hbL
    rwa [nrm_rt ha'L.aestronglyMeasurable] at h
  have hInner := hFint.integral_prod_left
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hInner, ?_⟩
  have h1 : ∀ x, star (a (x * φ t) - a x) * b x =
      ∫ s in Set.Ioc 0 t, star (a' (x * φ s)) * b x := by
    intro x
    rw [← ftc hφc hφ0 ha' hd x t, intervalIntegral.integral_of_le ht, integral_mul_const]
    congr 1
    have h := integral_conj (μ := volume.restrict (Set.Ioc (0:ℝ) t)) (f := fun s => a' (x * φ s))
    simp only [starRingEnd_apply] at h
    exact h.symm
  have hL : pr μ (fun x => a (x * φ t)) b - pr μ a b = ∫ x, star (a (x * φ t) - a x) * b x ∂μ := by
    rw [← pr_sub_left (memLp_rt haL (φ t)) haL hbL]
    rfl
  rw [hL, intervalIntegral.integral_of_le ht]
  simp_rw [h1]
  exact (integral_integral_swap (f := fun s x => star (a' (x * φ s)) * b x) hFint).symm

theorem small_zero {D : ℂ} {C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖D‖ ≤ t * C) : D = 0 := by
  by_contra hD
  have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have h1 := h 1 one_pos le_rfl
  have hC : 0 < C := by linarith
  have hC0 : C ≠ 0 := hC.ne'
  have ht0 : 0 < min 1 (‖D‖ / (2 * C)) := lt_min one_pos (div_pos hpos (by linarith))
  have ht1 : min 1 (‖D‖ / (2 * C)) ≤ 1 := min_le_left _ _
  have ht2 : min 1 (‖D‖ / (2 * C)) ≤ ‖D‖ / (2 * C) := min_le_right _ _
  have h2 := h _ ht0 ht1
  have h3 : min 1 (‖D‖ / (2 * C)) * C ≤ ‖D‖ / 2 := by
    calc min 1 (‖D‖ / (2 * C)) * C ≤ ‖D‖ / (2 * C) * C := mul_le_mul_of_nonneg_right ht2 hC.le
      _ = ‖D‖ / 2 := by field_simp <;> ring
  linarith

private theorem negder_lemma {φ : ℝ → G} {a a' : G → ℂ}
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t) :
    ∀ x t, HasDerivAt (fun s => a (x * φ (-s))) (-a' (x * φ (-t))) t := by
  intro x t
  have h := (hd x (-t)).scomp t (hasDerivAt_id t).neg
  simpa [Function.comp_def] using h

private theorem inv_lemma_2 {φ : ℝ → G} (hφ0 : φ 0 = 1) (hφa : ∀ s t, φ (s + t) = φ s * φ t) (s : ℝ) :
    (φ s)⁻¹ = φ (-s) := by
  have h : φ s * φ (-s) = 1 := by
    rw [← hφa]
    simp [hφ0]
  exact (eq_inv_of_mul_eq_one_right h).symm

private theorem lin_lemma_3 {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1)
    (hφa : ∀ s t, φ (s + t) = φ s * φ t) {a a' b b' : G → ℂ}
    (ha' : Continuous a') (hb : Continuous b) (hb' : Continuous b')
    (haL : MemLp a 2 μ) (ha'L : MemLp a' 2 μ) (hbL : MemLp b 2 μ) (hb'L : MemLp b' 2 μ)
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t)
    (hdb : ∀ x t, HasDerivAt (fun s => b (x * φ s)) (b' (x * φ t)) t) {t : ℝ} (ht : 0 ≤ t) :
    ‖(pr μ (fun x => a (x * φ t)) b - pr μ a b) - (t : ℂ) * pr μ a' b‖ ≤
      t * (t * (nrm μ a' * nrm μ b')) := by
  have hψc : Continuous fun s => φ (-s) := hφc.comp continuous_neg
  obtain ⟨hI, hE⟩ := incr hφc hφ0 ha' hb haL ha'L hbL hd ht
  have hbd : ∀ s ∈ Set.uIoc 0 t,
      ‖pr μ (fun x => a' (x * φ s)) b - pr μ a' b‖ ≤ t * (nrm μ a' * nrm μ b') := by
    intro s hs
    rw [Set.uIoc_of_le ht] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have e1 : pr μ (fun x => a' (x * φ s)) b = pr μ a' (fun x => b (x * φ (-s))) := by
      rw [pr_shift, inv_lemma_2 hφ0 hφa]
    have e2 : pr μ (fun x => b (x * φ (-s))) a' - pr μ b a' =
        ∫ r in (0:ℝ)..s, pr μ (fun x => -b' (x * φ (-r))) a' :=
      (incr (φ := fun s => φ (-s)) hψc (by simp [hφ0]) (a' := fun y => -b' y) hb'.neg ha' hbL
        hb'L.neg ha'L (negder_lemma hdb) hs0).2
    have e3 : pr μ (fun x => a' (x * φ s)) b - pr μ a' b =
        star (pr μ (fun x => b (x * φ (-s))) a' - pr μ b a') := by
      rw [e1, star_sub, pr_star, pr_star]
    have hC : ∀ r ∈ Set.uIoc 0 s, ‖pr μ (fun x => -b' (x * φ (-r))) a'‖ ≤ nrm μ b' * nrm μ a' := by
      intro r _
      have h := pr_bound (memLp_rt hb'L.neg (φ (-r))) ha'L
      have hn : nrm μ (fun x => (-b') (x * φ (-r))) = nrm μ b' := by
        rw [nrm_rt hb'L.neg.aestronglyMeasurable]
        unfold nrm
        rw [eLpNorm_neg]
      rw [hn] at h
      exact h
    rw [e3, norm_star, e2]
    calc _ ≤ (nrm μ b' * nrm μ a') * |s - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hC
      _ ≤ t * (nrm μ a' * nrm μ b') := by
        rw [sub_zero, abs_of_nonneg hs0]
        have h1 : 0 ≤ nrm μ a' := ENNReal.toReal_nonneg
        have h2 : 0 ≤ nrm μ b' := ENNReal.toReal_nonneg
        have h3 : 0 ≤ nrm μ a' * nrm μ b' := mul_nonneg h1 h2
        nlinarith [hs.2]
  have hmain : pr μ (fun x => a (x * φ t)) b - pr μ a b - (t : ℂ) * pr μ a' b =
      ∫ s in (0:ℝ)..t, (pr μ (fun x => a' (x * φ s)) b - pr μ a' b) := by
    rw [intervalIntegral.integral_sub hI intervalIntegrable_const, intervalIntegral.integral_const, ← hE,
      sub_zero, Complex.real_smul]
  rw [hmain]
  calc _ ≤ (t * (nrm μ a' * nrm μ b')) * |t - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = _ := by rw [sub_zero, abs_of_nonneg ht]; ring

theorem skew {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) (hφa : ∀ s t, φ (s + t) = φ s * φ t)
    {u u' v v' : G → ℂ} (hu : Continuous u) (hu' : Continuous u') (hv : Continuous v)
    (hv' : Continuous v')
    (huL : MemLp u 2 μ) (hu'L : MemLp u' 2 μ) (hvL : MemLp v 2 μ) (hv'L : MemLp v' 2 μ)
    (hdu : ∀ x t, HasDerivAt (fun s => u (x * φ s)) (u' (x * φ t)) t)
    (hdv : ∀ x t, HasDerivAt (fun s => v (x * φ s)) (v' (x * φ t)) t) :
    pr μ u' v = -pr μ u v' := by
  have hψc : Continuous fun s => φ (-s) := hφc.comp continuous_neg
  have hψa : ∀ s t, φ (-(s + t)) = φ (-s) * φ (-t) := fun s t => by rw [neg_add, hφa]
  have hnv : nrm μ (fun y => -v' y) = nrm μ v' := by
    unfold nrm
    rw [show (fun y => -v' y) = -v' from rfl, eLpNorm_neg]
  have hnu : nrm μ (fun y => -u' y) = nrm μ u' := by
    unfold nrm
    rw [show (fun y => -u' y) = -u' from rfl, eLpNorm_neg]
  suffices h : pr μ u' v + pr μ u v' = 0 by linear_combination h
  apply small_zero (C := 2 * (nrm μ u' * nrm μ v'))
  intro t ht0 ht1
  have E1 : ‖(pr μ (fun x => u (x * φ t)) v - pr μ u v) - (t : ℂ) * pr μ u' v‖ ≤
      t * (t * (nrm μ u' * nrm μ v')) :=
    lin_lemma_3 hφc hφ0 hφa hu' hv hv' huL hu'L hvL hv'L hdu hdv ht0.le
  have E2 : ‖(pr μ (fun x => v (x * φ (-t))) u - pr μ v u) - (t : ℂ) * pr μ (fun y => -v' y) u‖ ≤
      t * (t * (nrm μ (fun y => -v' y) * nrm μ (fun y => -u' y))) :=
    lin_lemma_3 (φ := fun s => φ (-s)) hψc (by simp [hφ0]) hψa hv'.neg hu hu'.neg hvL hv'L.neg huL
      hu'L.neg (negder_lemma hdv) (negder_lemma hdu) ht0.le
  rw [hnv, hnu] at E2
  have e1 : pr μ (fun x => u (x * φ t)) v = pr μ u (fun x => v (x * φ (-t))) := by
    rw [pr_shift, inv_lemma_2 hφ0 hφa]
  have e2 : star ((pr μ (fun x => v (x * φ (-t))) u - pr μ v u) - (t : ℂ) * pr μ (fun y => -v' y) u) =
      (pr μ (fun x => u (x * φ t)) v - pr μ u v) + (t : ℂ) * pr μ u v' := by
    rw [star_sub, star_sub, star_mul', pr_star, pr_star, pr_star, e1, Complex.star_def,
      Complex.conj_ofReal, pr_neg_right]
    ring
  have E3 : ‖(pr μ (fun x => u (x * φ t)) v - pr μ u v) + (t : ℂ) * pr μ u v'‖ ≤
      t * (t * (nrm μ u' * nrm μ v')) := by
    rw [← e2, norm_star]
    linarith [E2]
  have key : (t : ℂ) * (pr μ u' v + pr μ u v') =
      ((pr μ (fun x => u (x * φ t)) v - pr μ u v) + (t : ℂ) * pr μ u v') -
        ((pr μ (fun x => u (x * φ t)) v - pr μ u v) - (t : ℂ) * pr μ u' v) := by ring
  have hn : ‖(t : ℂ) * (pr μ u' v + pr μ u v')‖ ≤ 2 * (t * (t * (nrm μ u' * nrm μ v'))) := by
    rw [key]
    exact (norm_sub_le _ _).trans (by linarith)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le] at hn
  exact le_of_mul_le_mul_left (by linarith : t * ‖pr μ u' v + pr μ u v'‖ ≤
    t * (t * (2 * (nrm μ u' * nrm μ v')))) ht0

end Flow

end ReciprocityTheory.ChartRestriction.DS.UnitA

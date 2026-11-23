import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsSphereLaw
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanSlice
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory Set Real

noncomputable section

namespace SphereLawFirstCoord

open SphereMean

theorem volume_annulus {a : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    volume {w : ℂ | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < s} = ENNReal.ofReal (s - a) * NNReal.pi := by
  rcases le_or_gt s a with hsa | hsa
  · have : {w : ℂ | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < s} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro h
      linarith
    rw [this, measure_empty, ENNReal.ofReal_of_nonpos (by linarith), zero_mul]
  · have hset : {w : ℂ | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < s} = Metric.ball 0 √s \ Metric.ball 0 √a := by
      ext w
      simp only [mem_ofPred_eq, mem_sdiff, Metric.mem_ball, dist_zero_right, not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(Real.lt_sqrt (norm_nonneg w)).2 h2, Real.sqrt_le_iff.2 ⟨norm_nonneg w, h1⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(Real.sqrt_le_iff.1 h2).2, (Real.lt_sqrt (norm_nonneg w)).1 h1⟩
    rw [hset, measure_sdiff (Metric.ball_subset_ball (Real.sqrt_le_sqrt hsa.le))
      measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne, Complex.volume_ball,
      Complex.volume_ball, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (ha.trans hsa.le), Real.sq_sqrt ha,
      ← ENNReal.sub_mul (fun _ _ ↦ ENNReal.coe_ne_top), ENNReal.ofReal_sub _ ha]

theorem volume_capSet {m : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    volume {v : Fin (m + 1) → ℂ | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      (∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y / (1 - c))) * NNReal.pi := by
  have h1c : 0 < 1 - c := by linarith
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℂ) 0
  set A : Set (ℂ × (Fin m → ℂ)) :=
    {p | c * (‖p.1‖ ^ 2 + sqNorm p.2) ≤ ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 + sqNorm p.2 < 1} with hA_def
  have hA : MeasurableSet A := by
    have h1 : Continuous fun p : ℂ × (Fin m → ℂ) ↦ ‖p.1‖ ^ 2 + sqNorm p.2 :=
      ((continuous_norm.comp continuous_fst).pow 2).add ((continuous_sqNorm m).comp continuous_snd)
    exact (measurableSet_le (continuous_const.mul h1).measurable
      ((continuous_norm.comp continuous_fst).pow 2).measurable).inter
      (measurableSet_lt h1.measurable measurable_const)
  have hpre : {v : Fin (m + 1) → ℂ | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℂ) 0 ⁻¹' A := by
    ext v
    simp only [mem_ofPred_eq, mem_preimage, piFinSuccAbove_zero_apply, hA_def, sqNorm_succ]
  rw [hpre, he.measure_preimage hA.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply_symm hA, ← lintegral_mul_const' _ _ ENNReal.coe_ne_top]
  congr 1
  funext y
  have hfib : (fun x : ℂ ↦ (x, y)) ⁻¹' A =
      {w : ℂ | c * sqNorm y / (1 - c) ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < 1 - sqNorm y} := by
    ext w
    simp only [mem_preimage, hA_def, mem_ofPred_eq, div_le_iff₀ h1c]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  rw [hfib, volume_annulus (div_nonneg (mul_nonneg hc0 (sqNorm_nonneg y)) h1c.le)]
  congr 2
  field_simp
  ring

theorem lintegral_scale {m : ℕ} {c : ℝ} (hc1 : c < 1) :
    ∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y / (1 - c)) =
      ENNReal.ofReal ((1 - c) ^ m) * ∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y) := by
  have h1c : 0 < 1 - c := by linarith
  have hr0 : √(1 - c) ≠ 0 := (Real.sqrt_pos.2 h1c).ne'
  set f : (Fin m → ℂ) → ENNReal := fun y ↦ ENNReal.ofReal (1 - sqNorm y / (1 - c)) with hf
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub ((measurable_sqNorm m).div_const _))
  have hfr : ∀ y, f (√(1 - c) • y) = ENNReal.ofReal (1 - sqNorm y) := by
    intro y
    simp only [hf, sqNorm_smul, Real.sq_sqrt h1c.le]
    congr 2
    field_simp
  have key : ∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y) =
      ENNReal.ofReal (((1 - c) ^ m)⁻¹) * ∫⁻ y, f y := by
    simp_rw [← hfr]
    have hmap' : ∫⁻ y, f (√(1 - c) • y) =
        ∫⁻ y, f y ∂(Measure.map (fun y : Fin m → ℂ ↦ √(1 - c) • y) volume) :=
      (lintegral_map hfm (by fun_prop)).symm
    rw [hmap', Measure.map_addHaar_smul (volume : Measure (Fin m → ℂ)) hr0, lintegral_smul_measure,
      finrank_fun_complex, pow_mul, Real.sq_sqrt h1c.le, abs_of_pos (inv_pos.2 (pow_pos h1c m))]
    rfl
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul (pow_pos h1c m).le,
    mul_inv_cancel₀ (pow_pos h1c m).ne', ENNReal.ofReal_one, one_mul]

theorem volume_capSet_eq {m : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    volume {v : Fin (m + 1) → ℂ | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      ENNReal.ofReal ((1 - c) ^ m) * volume (ballSet (m + 1) 1) := by
  have h0 := volume_capSet (m := m) le_rfl zero_lt_one
  have hb : {v : Fin (m + 1) → ℂ | 0 * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      ballSet (m + 1) 1 := by
    ext v
    simp [ballSet]
  rw [hb] at h0
  simp only [sub_zero, div_one] at h0
  rw [volume_capSet hc0 hc1, lintegral_scale hc1, mul_assoc, ← h0]

theorem density_Ici (k : ℕ) (c : ℝ) :
    (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal
        (Set.indicator (Set.Icc 0 1) (fun x ↦ (k + 1 : ℝ) * (1 - x) ^ k) x)) (Ici c) =
      ENNReal.ofReal ((1 - min (max c 0) 1) ^ (k + 1)) := by
  rw [withDensity_apply _ measurableSet_Ici]
  have hind : ∀ x : ℝ, ENNReal.ofReal (Set.indicator (Set.Icc 0 1)
      (fun x ↦ (k + 1 : ℝ) * (1 - x) ^ k) x) =
      Set.indicator (Set.Icc 0 1) (fun x ↦ ENNReal.ofReal ((k + 1 : ℝ) * (1 - x) ^ k)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [hx]
  simp_rw [hind]
  rw [setLIntegral_indicator measurableSet_Icc]
  have hI : Icc (0 : ℝ) 1 ∩ Ici c = Icc (max c 0) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc, max_le_iff]
    tauto
  rw [hI]
  rcases le_or_gt (max c 0) 1 with hd | hd
  · rw [min_eq_left hd, ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun x ↦ x ^ k) (1 : ℝ), integral_pow]
      congr 1
      field_simp
      simp
    · exact (by fun_prop : Continuous fun x : ℝ ↦ (k + 1 : ℝ) * (1 - x) ^ k).integrableOn_Icc
    · refine ae_restrict_of_forall_mem measurableSet_Icc fun x hx ↦ ?_
      exact mul_nonneg (by positivity) (pow_nonneg (by linarith [hx.2]) k)
  · rw [Icc_eq_empty (not_le.2 hd), Measure.restrict_empty, lintegral_zero_measure,
      min_eq_right hd.le]
    simp

theorem law_Ici (k : ℕ) (c : ℝ) :
    ((sphereLaw (k + 1 + 1)).map (fun z ↦ ‖z 0‖ ^ 2)) (Ici c) =
      ENNReal.ofReal ((1 - min (max c 0) 1) ^ (k + 1)) := by
  have hGm : Measurable fun (u : Fin 1 × Fin (k + 1 + 1) → ℂ) (j : Fin (k + 1 + 1)) ↦
      sphereNormalize (HermNorm.std (k + 1 + 1)) 1 u (0, j) := by
    unfold sphereNormalize
    simp only [HermNorm.std_norm_eq]
    fun_prop
  have hFm : Measurable fun z : Fin (k + 1 + 1) → ℂ ↦ ‖z 0‖ ^ 2 := by fun_prop
  have hBm : MeasurableSet (sphereBall (HermNorm.std (k + 1 + 1)) 1) :=
    (isOpen_sphereBall_std _).measurableSet
  rw [Measure.map_apply hFm measurableSet_Ici, sphereLaw,
    Measure.map_apply hGm (hFm measurableSet_Ici), cond_apply hBm]

  set eq := Equiv.uniqueProd (Fin (k + 1 + 1)) (Fin 1)
  set P := MeasurableEquiv.piCongrLeft (fun _ : Fin (k + 1 + 1) ↦ ℂ) eq
  have hP : MeasurePreserving P volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin (k + 1 + 1) ↦ ℂ) eq
  have hPapp : ∀ u j, P u j = u (0, j) := by
    intro u j
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin (k + 1 + 1) ↦ ℂ) eq u (0, j)
    simpa [eq] using this
  have hPu : ∀ u : Fin 1 × Fin (k + 1 + 1) → ℂ, (fun j ↦ u (0, j)) = P u :=
    fun u ↦ funext fun j ↦ (hPapp u j).symm
  have hB : sphereBall (HermNorm.std (k + 1 + 1)) 1 = P ⁻¹' ballSet (k + 1 + 1) 1 := by
    ext u
    simp only [sphereBall, mem_ofPred_eq, mem_preimage, ballSet, std_norm_eq, Fin.forall_fin_one,
      hPu, Real.sqrt_lt' one_pos, one_pow]
  set T : Set (Fin (k + 1 + 1) → ℂ) :=
    {v | sqNorm v < 1 ∧ c ≤ ‖((√(sqNorm v) : ℝ) : ℂ)⁻¹ * v 0‖ ^ 2} with hT_def
  have hT : sphereBall (HermNorm.std (k + 1 + 1)) 1 ∩
      ((fun (u : Fin 1 × Fin (k + 1 + 1) → ℂ) (j : Fin (k + 1 + 1)) ↦
        sphereNormalize (HermNorm.std (k + 1 + 1)) 1 u (0, j)) ⁻¹'
        ((fun z : Fin (k + 1 + 1) → ℂ ↦ ‖z 0‖ ^ 2) ⁻¹' Ici c)) = P ⁻¹' T := by
    rw [hB]
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Ici, sphereNormalize, std_norm_eq, hPu, hT_def,
      mem_ofPred_eq, ballSet, hPapp]
  rw [hT, hB, hP.measure_preimage_equiv, hP.measure_preimage_equiv]
  have hV0 := (volume_ballSet_one_pos (k + 1 + 1)).ne'
  have hVt := volume_ballSet_one_ne_top (k + 1 + 1)
  have hnorm : ∀ v : Fin (k + 1 + 1) → ℂ,
      ‖((√(sqNorm v) : ℝ) : ℂ)⁻¹ * v 0‖ ^ 2 = ‖v 0‖ ^ 2 / sqNorm v := by
    intro v
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      inv_pow, Real.sq_sqrt (sqNorm_nonneg v)]
    ring

  have hTpos : 0 < c → T = {v | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} \ {0} := by
    intro hc
    ext v
    simp only [hT_def, mem_ofPred_eq, mem_sdiff, mem_singleton_iff, hnorm]
    by_cases hv : v = 0
    · subst hv
      simp [sqNorm]
      exact hc
    · have hs := sqNorm_pos_of_ne_zero hv
      rw [le_div_iff₀ hs]
      tauto
  rcases le_or_gt c 0 with hc | hc
  · have hTB : T = ballSet (k + 1 + 1) 1 := by
      ext v
      simp only [hT_def, mem_ofPred_eq, ballSet, and_iff_left_iff_imp]
      intro _
      exact hc.trans (by positivity)
    rw [hTB, ENNReal.inv_mul_cancel hV0 hVt, max_eq_right hc, min_eq_left zero_le_one]
    simp
  rcases lt_or_ge c 1 with hc1 | hc1
  · rw [hTpos hc, measure_sdiff_null (volume_singleton_zero _), volume_capSet_eq hc.le hc1,
      ← mul_assoc, mul_comm _ (ENNReal.ofReal _), mul_assoc, ENNReal.inv_mul_cancel hV0 hVt,
      mul_one, max_eq_left hc.le, min_eq_left hc1.le]
  ·
    have he := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1 + 1) ↦ ℂ) 0
    have hsub : T ⊆ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1 + 1) ↦ ℂ) 0 ⁻¹'
        (univ ×ˢ {0}) := by
      rw [hTpos hc]
      rintro v ⟨⟨h1, _⟩, hv⟩
      simp only [mem_preimage, piFinSuccAbove_zero_apply, mem_prod, mem_univ, true_and,
        mem_singleton_iff]
      by_contra htl
      have := sqNorm_pos_of_ne_zero htl
      rw [sqNorm_succ] at h1
      nlinarith [sqNorm_nonneg (Fin.tail v), norm_nonneg (v 0)]
    have h0 : volume T = 0 := by
      refine measure_mono_null hsub ?_
      rw [he.measure_preimage (MeasurableSet.univ.prod (measurableSet_singleton _)).nullMeasurableSet,
        Measure.volume_eq_prod, Measure.prod_prod, volume_singleton_zero, mul_zero]
    rw [h0, mul_zero, max_eq_left hc.le, min_eq_right hc1, sub_self, zero_pow (Nat.succ_ne_zero _),
      ENNReal.ofReal_zero]

end SphereLawFirstCoord

theorem SphereLawFirstCoord.proof : SphereLawFirstCoord.Statement := by
  intro N hN
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  show (sphereLaw (k + 1 + 1)).map (fun z ↦ ‖z 0‖ ^ 2) = _
  have hd : (fun x : ℝ ↦ ENNReal.ofReal (Set.indicator (Set.Icc 0 1)
      (fun x ↦ ((k + 1 + 1 : ℕ) - 1 : ℝ) * (1 - x) ^ (k + 1 + 1 - 2)) x)) =
      fun x ↦ ENNReal.ofReal (Set.indicator (Set.Icc 0 1) (fun x ↦ (k + 1 : ℝ) * (1 - x) ^ k) x) := by
    have h2 : k + 1 + 1 - 2 = k := by omega
    simp only [h2]
    push_cast
    ring_nf
  rw [hd]
  have := (sphereLaw (k + 1 + 1)).isFiniteMeasure_map fun z : Fin (k + 1 + 1) → ℂ ↦ ‖z 0‖ ^ 2
  refine Measure.ext_of_Ici _ _ fun c ↦ ?_
  rw [SphereLawFirstCoord.law_Ici, SphereLawFirstCoord.density_Ici]

end

end GroundTheory.Heights₂.Heights

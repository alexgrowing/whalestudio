import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Metric Set

lemma rsm_pow_gauss (k : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ k * Real.exp (-y ^ 2) = (1 / 2) * Real.Gamma ((k + 1) / 2) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  first
    | (have h := integral_rpow_mul_exp_neg_rpow (two_pos : (0 : ℝ) < 2) hk
       simp only [Real.rpow_natCast, Real.rpow_two] at h
       exact h)
    | (have h := integral_rpow_mul_exp_neg_mul_rpow (two_pos : (0 : ℝ) < 2) hk one_pos
       simp only [Real.rpow_natCast, Real.rpow_two, neg_mul, one_mul, Real.one_rpow] at h
       rw [h]
       norm_num)

lemma rsm_pow_gauss_int (k : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ k * Real.exp (-y ^ 2)) (Ioi 0) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos hk
  simp only [Real.rpow_natCast, neg_mul, one_mul] at h
  exact h

lemma rsm_finrank (N : ℕ) : Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) = 2 * N := by
  first
    | rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]
    | rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
    | rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin N)), Complex.finrank_real_complex,
        finrank_euclideanSpace, Fintype.card_fin]
    | simp [finrank_real_of_complex]

lemma rsm_gauss_total (N : ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin N), Real.exp (-‖z‖ ^ 2) = Real.pi ^ N := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℂ (Fin N)) one_pos
  simp only [neg_mul, one_mul, div_one] at h
  first | rw [h] | erw [h]
  rw [rsm_finrank, show ((↑(2 * N) : ℝ) / 2) = ((N : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

lemma rsm_gauss_integrable (N : ℕ) :
    Integrable (fun z : EuclideanSpace ℂ (Fin N) => Real.exp (-‖z‖ ^ 2)) := by
  first
    | exact Integrable.of_integral_ne_zero (by rw [rsm_gauss_total]; positivity)
    | (have h := GaussianFourier.integrable_rexp_neg_mul_sq_norm (V := EuclideanSpace ℂ (Fin N)) one_pos
       simp only [neg_mul, one_mul] at h
       exact h)

lemma rsm_tail (N : ℕ) (hN : 1 ≤ N) :
    ∫ y in Ioi (0 : ℝ), y ^ (2 * N - 1) *
        (Set.indicator (Ioi (Real.sqrt (2 * N))) (fun y => Real.exp (-y ^ 2)) y)
      ≤ (1 / 2) * ∫ y in Ioi (0 : ℝ), y ^ (2 * N - 1) * Real.exp (-y ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have hk : 2 * N - 1 + 2 = 2 * N + 1 := by omega
  have hI : ∫ y in Ioi (0 : ℝ), (1 / (2 * (N : ℝ))) * (y ^ (2 * N + 1) * Real.exp (-y ^ 2))
      = (1 / 2) * ∫ y in Ioi (0 : ℝ), y ^ (2 * N - 1) * Real.exp (-y ^ 2) := by
    first | rw [integral_const_mul] | rw [integral_mul_left]
    rw [rsm_pow_gauss, rsm_pow_gauss]
    have e1 : ((↑(2 * N + 1) : ℝ) + 1) / 2 = (N : ℝ) + 1 := by push_cast; ring
    have e2 : ((↑(2 * N - 1) : ℝ) + 1) / 2 = (N : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * N)]
      push_cast
      ring
    rw [e1, e2, Real.Gamma_add_one hN1]
    field_simp
    try ring
  rw [← hI]
  refine integral_mono_of_nonneg ?_ ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    exact mul_nonneg (pow_nonneg hy'.le _)
      (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
  · exact Integrable.const_mul (rsm_pow_gauss_int (2 * N + 1)) _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    by_cases h : y ∈ Ioi (Real.sqrt (2 * N))
    · rw [Set.indicator_of_mem h]
      have hs : Real.sqrt (2 * N) < y := h
      have hy2 : 2 * (N : ℝ) ≤ y ^ 2 := by
        nlinarith [Real.sqrt_nonneg (2 * (N : ℝ)), Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * N)]
      have ha : 0 ≤ y ^ (2 * N - 1) * Real.exp (-y ^ 2) :=
        mul_nonneg (pow_nonneg hy'.le _) (Real.exp_pos _).le
      have hq : (1 : ℝ) ≤ y ^ 2 / (2 * N) := by
        first
          | exact (one_le_div (by positivity)).mpr hy2
          | (rw [le_div_iff₀ (by positivity)]; linarith)
      calc y ^ (2 * N - 1) * Real.exp (-y ^ 2) = y ^ (2 * N - 1) * Real.exp (-y ^ 2) * 1 := by ring
        _ ≤ y ^ (2 * N - 1) * Real.exp (-y ^ 2) * (y ^ 2 / (2 * N)) :=
          mul_le_mul_of_nonneg_left hq ha
        _ = 1 / (2 * (N : ℝ)) * (y ^ (2 * N + 1) * Real.exp (-y ^ 2)) := by
          rw [← hk, pow_add]
          ring
    · have h0 : Set.indicator (Ioi (Real.sqrt (2 * N))) (fun y => Real.exp (-y ^ 2)) y = 0 := by
        simp only [Set.indicator_apply, h, if_false]
      rw [h0, mul_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hy'.le _) (Real.exp_pos _).le)

private lemma half_le_of_tail_le_half (P B C d V A T : ℝ) (hd : 0 ≤ d) (hV : 0 ≤ V) (hT : T ≤ 1 / 2 * A)
    (htot : P = d * (V * A)) (htail : C = d * (V * T)) (hsum : B + C = P) : P / 2 ≤ B := by
  have h1 : V * T ≤ V * (1 / 2 * A) := mul_le_mul_of_nonneg_left hT hV
  have h2 : d * (V * T) ≤ d * (V * (1 / 2 * A)) := mul_le_mul_of_nonneg_left h1 hd
  have h3 : d * (V * (1 / 2 * A)) = P / 2 := by rw [htot]; ring
  linarith

lemma rsm_ball_mass (N : ℕ) :
    Real.pi ^ N / 2 ≤
      ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)), Real.exp (-‖z‖ ^ 2) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hz : ∀ z : EuclideanSpace ℂ (Fin 0), z = 0 := by
      intro z
      first
        | exact Subsingleton.elim z 0
        | exact PiLp.ext (fun i => i.elim0)
        | (ext i; exact i.elim0)
    have hb : ∀ r : ℝ, 0 ≤ r → closedBall (0 : EuclideanSpace ℂ (Fin 0)) r = univ := by
      intro r hr
      ext z
      rw [hz z]
      simp [hr]
    rw [hb _ (Real.sqrt_nonneg _), Measure.restrict_univ, rsm_gauss_total]
    norm_num
  · haveI : Nontrivial (EuclideanSpace ℂ (Fin N)) := by
      first
        | exact Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [rsm_finrank]; omega)
        | exact FiniteDimensional.nontrivial_of_finrank_pos (R := ℝ) (by rw [rsm_finrank]; omega)
        | exact Module.finrank_pos_iff.mp (by rw [rsm_finrank]; omega)
        | infer_instance
    have hsum : (∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)), Real.exp (-‖z‖ ^ 2))
        + (∫ z in (closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)))ᶜ, Real.exp (-‖z‖ ^ 2))
        = ∫ z : EuclideanSpace ℂ (Fin N), Real.exp (-‖z‖ ^ 2) :=
      integral_add_compl measurableSet_closedBall (rsm_gauss_integrable N)
    have htot := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℂ (Fin N)))
      (fun y : ℝ => Real.exp (-y ^ 2))
    have htail0 := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℂ (Fin N)))
      (fun y : ℝ => Set.indicator (Ioi (Real.sqrt (2 * N))) (fun y => Real.exp (-y ^ 2)) y)
    simp only [smul_eq_mul, nsmul_eq_mul, rsm_finrank] at htot htail0
    have htail : ∫ z in (closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)))ᶜ, Real.exp (-‖z‖ ^ 2)
        = ∫ z : EuclideanSpace ℂ (Fin N),
            Set.indicator (Ioi (Real.sqrt (2 * N))) (fun y => Real.exp (-y ^ 2)) ‖z‖ := by
      rw [← integral_indicator measurableSet_closedBall.compl]
      congr 1
      ext z
      by_cases h : ‖z‖ ≤ Real.sqrt (2 * N)
      · have h' : ¬ (Real.sqrt (2 * N) < ‖z‖) := not_lt.mpr h
        have hz1 : z ∉ (closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)))ᶜ := fun hc =>
          (Set.mem_compl_iff _ _).mp hc (mem_closedBall.mpr (by rwa [dist_zero_right]))
        simp only [Set.indicator_apply, Set.mem_compl_iff, mem_closedBall, dist_zero_right, Set.mem_Ioi,
          h, h', not_true_eq_false, not_false_eq_true, if_true, if_false]
        first
          | exact Set.indicator_of_not_mem hz1 _
          | exact Set.indicator_of_notMem hz1 _
      · have h' : Real.sqrt (2 * N) < ‖z‖ := not_le.mp h
        have hz1 : z ∈ (closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)))ᶜ :=
          (Set.mem_compl_iff _ _).mpr (fun hb => h (by rwa [mem_closedBall, dist_zero_right] at hb))
        simp only [Set.indicator_apply, Set.mem_compl_iff, mem_closedBall, dist_zero_right, Set.mem_Ioi,
          h, h', not_true_eq_false, not_false_eq_true, if_true, if_false]
        exact Set.indicator_of_mem hz1 _
    rw [← rsm_gauss_total N]
    exact half_le_of_tail_le_half _ _ _ _ _ _ _ (by positivity)
      (by first | positivity | exact measureReal_nonneg | exact ENNReal.toReal_nonneg)
      (rsm_tail N (by omega)) htot (htail.trans htail0) hsum

lemma rsm_mean (N : ℕ) (F : EuclideanSpace ℂ (Fin N) → ℂ) (hF : Differentiable ℂ F)
    (z : EuclideanSpace ℂ (Fin N)) :
    ‖F 0‖ ^ 2 ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖F (circleMap 0 1 θ • z)‖ ^ 2 := by
  set h : ℂ → ℂ := fun w => F (w • z) ^ 2 with hh
  have hd : Differentiable ℂ h := by
    first
      | exact (hF.comp (differentiable_id.smul_const z)).pow 2
      | (rw [hh]; fun_prop)
  have hc := (hd.diffContOnCl (s := Metric.ball (0 : ℂ) 1)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul
    (Metric.mem_ball_self one_pos)
  have hI : (∮ w in C(0, 1), (w - 0)⁻¹ • h w)
      = Complex.I * ∫ θ in (0 : ℝ)..2 * Real.pi, h (circleMap 0 1 θ) := by
    first | rw [circleIntegral] | unfold circleIntegral
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hc0 : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
    simp only [deriv_circleMap, smul_eq_mul, sub_zero]
    rw [mul_comm (circleMap 0 1 θ) Complex.I, mul_assoc, mul_inv_cancel_left₀ hc0]
  rw [hI, smul_eq_mul] at hc
  have h0 : ‖F 0‖ ^ 2 = ‖h 0‖ := by simp [hh, norm_pow]
  have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * ‖Complex.I‖ = (2 * Real.pi)⁻¹ := by
    first
      | simp [abs_of_pos Real.pi_pos]
      | (simp [abs_of_pos Real.pi_pos]; ring)
      | (simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos])
  have hle : ‖∫ θ in (0 : ℝ)..2 * Real.pi, h (circleMap 0 1 θ)‖
      ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, ‖F (circleMap 0 1 θ • z)‖ ^ 2 := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans (le_of_eq ?_)
    simp [hh, norm_pow]
  rw [h0, ← hc, norm_mul, norm_mul]
  calc ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * (‖Complex.I‖ * ‖∫ θ in (0 : ℝ)..2 * Real.pi, h (circleMap 0 1 θ)‖)
      = (‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * ‖Complex.I‖)
          * ‖∫ θ in (0 : ℝ)..2 * Real.pi, h (circleMap 0 1 θ)‖ := by ring
    _ ≤ _ := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left hle (by positivity)

noncomputable def rsmRot (N : ℕ) (u : ℂ) (hu : ‖u‖ = 1) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin N) where
  toFun z := u • z
  invFun z := u⁻¹ • z
  map_add' x y := smul_add u x y
  map_smul' r x := by rw [RingHom.id_apply]; exact smul_comm u r x
  left_inv z := by
    have : u ≠ 0 := by rintro rfl; simp at hu
    simp [smul_smul, inv_mul_cancel₀ this]
  right_inv z := by
    have : u ≠ 0 := by rintro rfl; simp at hu
    simp [smul_smul, mul_inv_cancel₀ this]
  norm_map' z := by simp [norm_smul, hu]

lemma rsm_rot_int (N : ℕ) (F : EuclideanSpace ℂ (Fin N) → ℂ) (u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) :
    ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r, Real.exp (-‖z‖ ^ 2) * ‖F (u • z)‖ ^ 2
      = ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r, Real.exp (-‖z‖ ^ 2) * ‖F z‖ ^ 2 := by
  have hcoe : ∀ z, rsmRot N u hu z = u • z := fun z => rfl
  have hmp : MeasurePreserving (rsmRot N u hu) := (rsmRot N u hu).measurePreserving
  have hemb : MeasurableEmbedding (rsmRot N u hu) := by
    first
      | exact (rsmRot N u hu).toHomeomorph.measurableEmbedding
      | exact (rsmRot N u hu).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hpre : (rsmRot N u hu) ⁻¹' closedBall 0 r = closedBall 0 r := by
    ext z
    simp [hcoe, norm_smul, hu]
  calc ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r, Real.exp (-‖z‖ ^ 2) * ‖F (u • z)‖ ^ 2
      = ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r,
          (fun w => Real.exp (-‖w‖ ^ 2) * ‖F w‖ ^ 2) (rsmRot N u hu z) := by
        congr 1
        ext z
        simp only [hcoe, norm_smul, hu, one_mul]
    _ = ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r, Real.exp (-‖z‖ ^ 2) * ‖F z‖ ^ 2 := by
        have key := hmp.setIntegral_preimage_emb hemb
          (fun w => Real.exp (-‖w‖ ^ 2) * ‖F w‖ ^ 2) (closedBall 0 r)
        rw [hpre] at key
        exact key

lemma rsm_prod_int (N : ℕ) (F : EuclideanSpace ℂ (Fin N) → ℂ) (hF : Continuous F) (r : ℝ) :
    Integrable (fun p : EuclideanSpace ℂ (Fin N) × ℝ =>
        Real.exp (-‖p.1‖ ^ 2) * ‖F (circleMap 0 1 p.2 • p.1)‖ ^ 2)
      ((volume.restrict (closedBall 0 r)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
  have hc : Continuous fun p : EuclideanSpace ℂ (Fin N) × ℝ => circleMap 0 1 p.2 • p.1 :=
    ((continuous_circleMap 0 1).comp continuous_snd).smul continuous_fst
  have hg : Continuous fun p : EuclideanSpace ℂ (Fin N) × ℝ =>
      Real.exp (-‖p.1‖ ^ 2) * ‖F (circleMap 0 1 p.2 • p.1)‖ ^ 2 := by
    first
      | exact (Real.continuous_exp.comp ((continuous_fst.norm.pow 2).neg)).mul ((hF.comp hc).norm.pow 2)
      | fun_prop
  rw [Measure.prod_restrict]
  exact (hg.continuousOn.integrableOn_compact ((isCompact_closedBall 0 r).prod isCompact_Icc)).mono_set
    (Set.prod_mono subset_rfl Set.Ioc_subset_Icc_self)

theorem sq_norm_zero_le_gauss_ball {N : ℕ} (F : EuclideanSpace ℂ (Fin N) → ℂ)
    (hF : Differentiable ℂ F) :
    ‖F 0‖ ^ 2 ≤ 2 / Real.pi ^ N *
      ∫ z in Metric.closedBall 0 (Real.sqrt (2 * N)), ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  have hFc : Continuous F := hF.continuous
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hprod := rsm_prod_int N F hFc (Real.sqrt (2 * N))
  have hpt : ∀ z : EuclideanSpace ℂ (Fin N), ‖F 0‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
      (2 * Real.pi)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
        Real.exp (-‖z‖ ^ 2) * ‖F (circleMap 0 1 θ • z)‖ ^ 2 := by
    intro z
    have hm := rsm_mean N F hF z
    rw [← intervalIntegral.integral_of_le hpi.le, intervalIntegral.integral_const_mul]
    have he : 0 ≤ Real.exp (-‖z‖ ^ 2) := (Real.exp_pos _).le
    calc ‖F 0‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
        ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖F (circleMap 0 1 θ • z)‖ ^ 2)
            * Real.exp (-‖z‖ ^ 2) := mul_le_mul_of_nonneg_right hm he
      _ = _ := by ring
  have hJθ : ∀ θ : ℝ, ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)),
      Real.exp (-‖z‖ ^ 2) * ‖F (circleMap 0 1 θ • z)‖ ^ 2 =
      ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)),
      Real.exp (-‖z‖ ^ 2) * ‖F z‖ ^ 2 := by
    intro θ
    refine rsm_rot_int N F _ ?_ _
    first | simp | simp [norm_circleMap_zero] | simp [abs_circleMap_zero]
  have hswap : ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)),
        ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), Real.exp (-‖z‖ ^ 2) * ‖F (circleMap 0 1 θ • z)‖ ^ 2
      = ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)),
        Real.exp (-‖z‖ ^ 2) * ‖F (circleMap 0 1 θ • z)‖ ^ 2 :=
    integral_integral_swap hprod
  have hRHS : ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)),
        (2 * Real.pi)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
          Real.exp (-‖z‖ ^ 2) * ‖F (circleMap 0 1 θ • z)‖ ^ 2
      = ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)),
          ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
    first | rw [integral_const_mul] | rw [integral_mul_left]
    rw [hswap]
    simp only [hJθ]
    rw [← intervalIntegral.integral_of_le hpi.le, intervalIntegral.integral_const, smul_eq_mul, sub_zero,
      ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]
    congr 1
    ext z
    ring
  have hLHS : ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)),
        ‖F 0‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
      = ‖F 0‖ ^ 2 * ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)),
        Real.exp (-‖z‖ ^ 2) := by
    first | rw [integral_const_mul] | rw [integral_mul_left]
  have hmono : ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)),
        ‖F 0‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
      ≤ ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)),
        (2 * Real.pi)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
          Real.exp (-‖z‖ ^ 2) * ‖F (circleMap 0 1 θ • z)‖ ^ 2 := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · exact ae_of_all _ (fun z => mul_nonneg (by positivity) (Real.exp_pos _).le)
    · exact (hprod.integral_prod_left).const_mul _
    · exact ae_of_all _ hpt
  rw [hLHS, hRHS] at hmono
  have hmass := rsm_ball_mass N
  have hp : (0 : ℝ) < Real.pi ^ N := by positivity
  have ha : (0 : ℝ) ≤ ‖F 0‖ ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hmass ha
  have h2 : ‖F 0‖ ^ 2 * Real.pi ^ N = 2 * (‖F 0‖ ^ 2 * (Real.pi ^ N / 2)) := by ring
  have h3 : ‖F 0‖ ^ 2 * Real.pi ^ N ≤
      2 * ∫ z in Metric.closedBall (0 : EuclideanSpace ℂ (Fin N)) (Real.sqrt (2 * N)),
        ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by linarith
  rw [div_mul_eq_mul_div]
  first | exact (le_div_iff₀ hp).mpr h3 | exact (le_div_iff hp).mpr h3

end ReciprocityTheory.ChartRestriction.G.I2

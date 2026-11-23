import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.ExistsHarrisTaylorObjectOfLevelLift

open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.OM.SchDiff

section general

variable {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiff_iter {F : X → V} (hF : ContDiff ℝ ∞ F) (n : ℕ) : ContDiff ℝ ∞ (iteratedFDeriv ℝ n F) :=
  hF.iteratedFDeriv_right (by norm_cast)

theorem fderiv_iter_comm {F : X → V} (hF : ContDiff ℝ ∞ F) (h : X) (n : ℕ) (a : X) :
    fderiv ℝ (iteratedFDeriv ℝ n F) a h = iteratedFDeriv ℝ n (fun b => fderiv ℝ F b h) a := by
  induction n generalizing a with
  | zero =>
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((contDiff_iter hF 0).differentiable (by simp) a)]
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    ext m
    have hK := contDiff_iter hF n
    have hK' : ContDiff ℝ ∞ (fderiv ℝ (iteratedFDeriv ℝ n F)) := hK.fderiv_right (by norm_cast)
    have hd := hK'.differentiable (by simp) a
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((contDiff_iter hF (n + 1)).differentiable (by simp) a), iteratedFDeriv_succ_apply_left,
      ← funext ih]
    simp only [iteratedFDeriv_succ_apply_left]
    rw [fderiv_continuousMultilinear_apply_const_apply (hd.clm_apply (differentiableAt_const _)),
      fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
    have hs := (hK.contDiffAt (x := a)).isSymmSndFDerivAt (by simp; norm_cast)
    simp [hs.eq h (m 0)]

theorem taylor_iter {F : X → V} (hF : ContDiff ℝ ∞ F) (n : ℕ) (a h : X) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ b ∈ segment ℝ a (a + h), ‖iteratedFDeriv ℝ (n + 2) F b‖ ≤ M) :
    ‖iteratedFDeriv ℝ n F (a + h) - iteratedFDeriv ℝ n F a
      - iteratedFDeriv ℝ n (fun b => fderiv ℝ F b h) a‖ ≤ M * ‖h‖ * ‖h‖ := by
  have h1 : ∀ b ∈ segment ℝ a (a + h),
      ‖fderiv ℝ (iteratedFDeriv ℝ n F) b - fderiv ℝ (iteratedFDeriv ℝ n F) a‖ ≤ M * ‖h‖ := by
    intro b hb
    have h2 := (convex_segment a (a + h)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := iteratedFDeriv ℝ (n + 1) F) (C := M)
      (fun x _ => (contDiff_iter hF (n + 1)).differentiable (by simp) x)
      (fun x hx => by rw [norm_fderiv_iteratedFDeriv]; exact hM x hx)
      (left_mem_segment _ _ _) hb
    have h3 : ‖b - a‖ ≤ ‖h‖ := by
      simpa using norm_sub_le_of_mem_segment hb
    rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map]
    exact h2.trans (by gcongr)
  have h4 := (convex_segment a (a + h)).norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ)
      (f := iteratedFDeriv ℝ n F)
      (fun x _ => (contDiff_iter hF n).differentiable (by simp) x) h1
      (left_mem_segment _ _ _) (right_mem_segment _ _ _)
  rw [add_sub_cancel_left, fderiv_iter_comm hF] at h4
  exact h4

end general

section family

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iter_slice {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (n : ℕ) (p : P) (x : E) :
    iteratedFDeriv ℝ n (fun y => F (p, y)) x =
      (iteratedFDeriv ℝ n F (p, x)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  have h1 : (fun y => F (p, y)) = (fun q => F ((p, 0) + q)) ∘ ContinuousLinearMap.inr ℝ P E := by
    funext y; simp
  have h2 : ContDiff ℝ ∞ (fun q => F ((p, 0) + q)) := hF.comp (contDiff_const.add contDiff_id)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ h2 _ (by norm_cast; simp),
    iteratedFDeriv_comp_add_left]
  simp

theorem seminorm_remainder {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (z : P)
    (hb : ∀ k n : ℕ, ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n F (p, x)‖ ≤ C)
    (R D : P → SchwartzMap E ℂ) (hR : ∀ p, ⇑(R p) = fun x => F (p, x))
    (hD : ∀ v, ⇑(D v) = fun x => fderiv ℝ F (z, x) (v, 0)) (k n : ℕ) :
    ∃ C, ∀ v, ‖v‖ ≤ 1 → SchwartzMap.seminorm ℂ k n (R (z + v) - R z - D v) ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hb k (n + 2)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC z (by simp) 0)
  refine ⟨C, fun v hv => SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_⟩
  have hG : ContDiff ℝ ∞ (fun b => fderiv ℝ F b ((v, 0) : P × E)) :=
    (hF.fderiv_right (m := ∞) (by norm_cast)).clm_apply contDiff_const
  have e1 : iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x =
      iteratedFDeriv ℝ n (R (z + v)) x - iteratedFDeriv ℝ n (R z) x - iteratedFDeriv ℝ n (D v) x := by
    have : ⇑(R (z + v) - R z - D v) = ⇑(R (z + v)) - ⇑(R z) - ⇑(D v) := by
      funext y; simp
    rw [this, iteratedFDeriv_sub_apply (f := ⇑(R (z + v)) - ⇑(R z)) (((R (z + v)).smooth n).sub ((R z).smooth n)).contDiffAt
      ((D v).smooth n).contDiffAt, iteratedFDeriv_sub_apply ((R (z + v)).smooth n).contDiffAt
      ((R z).smooth n).contDiffAt]
  have e2 : iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x =
      (iteratedFDeriv ℝ n F ((z, x) + (v, 0)) - iteratedFDeriv ℝ n F (z, x)
        - iteratedFDeriv ℝ n (fun b => fderiv ℝ F b ((v, 0) : P × E)) (z, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
    rw [e1, hR, hR, hD, iter_slice hF, iter_slice hF, iter_slice hG]
    ext m
    simp
  rcases eq_or_lt_of_le (show 0 ≤ ‖x‖ ^ k by positivity) with h0 | h0
  · rw [← h0, zero_mul]; positivity
  have h3 := taylor_iter hF n (z, x) (v, 0) (M := C / ‖x‖ ^ k) (by positivity) (by
    rintro b ⟨s, t, hs, ht, hst, rfl⟩
    have : s • (z, x) + t • ((z, x) + (v, (0 : E))) = (z + t • v, x) := by
      obtain rfl : s = 1 - t := by linarith
      ext <;> simp <;> module
    rw [this, le_div_iff₀ h0, mul_comm]
    apply hC
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]
    nlinarith [norm_nonneg v])
  have h4 : ‖((v, 0) : P × E)‖ = ‖v‖ := by simp [Prod.norm_def]
  rw [h4] at h3
  have h5 : ‖iteratedFDeriv ℝ n (⇑(R (z + v) - R z - D v)) x‖ ≤ C / ‖x‖ ^ k * ‖v‖ * ‖v‖ := by
    rw [e2]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    refine le_trans (mul_le_of_le_one_right (norm_nonneg _) ?_) h3
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_inr_le_one _ _ _
  calc _ ≤ ‖x‖ ^ k * (C / ‖x‖ ^ k * ‖v‖ * ‖v‖) := by gcongr
    _ = _ := by field_simp

theorem hasFDerivAt_family {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (z : P)
    (hb : ∀ k n : ℕ, ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n F (p, x)‖ ≤ C)
    (R D : P → SchwartzMap E ℂ) (hR : ∀ p, ⇑(R p) = fun x => F (p, x))
    (hD : ∀ v, ⇑(D v) = fun x => fderiv ℝ F (z, x) (v, 0))
    (T : SchwartzMap E ℂ →L[ℂ] ℂ) (L : P →L[ℝ] ℂ) (hL : ∀ v, L v = T (D v)) :
    HasFDerivAt (fun p => T (R p)) L z := by
  obtain ⟨S, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (by
      change Continuous fun f => ‖T f‖
      fun_prop)
  choose B hB using seminorm_remainder hF z hb R D hR hD
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun v : P => ‖v‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C * ∑ i ∈ S, |B i.1 i.2|) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : P) one_pos] with v hv
  rw [mem_closedBall_zero_iff] at hv
  have h1 := hC (R (z + v) - R z - D v)
  have h2 : (S.sup (schwartzSeminormFamily ℂ E ℂ)) (R (z + v) - R z - D v) ≤
      (∑ i ∈ S, |B i.1 i.2|) * ‖v‖ ^ 2 := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => (hB i.1 i.2 v hv).trans ?_
    gcongr
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i : ℕ × ℕ => |B i.1 i.2|)
      (fun _ _ => abs_nonneg _) hi)
  rw [hL, ← map_sub, ← map_sub, Real.norm_of_nonneg (by positivity), mul_assoc]
  refine le_trans h1 ?_
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  gcongr

theorem bound_mul_translate {A : P × E → ℂ} (hA : Function.HasTemperateGrowth A) (s : SchwartzMap E ℂ)
    (l : P →L[ℝ] E) (z : P) (k n : ℕ) :
    ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun q : P × E => A q * s (q.2 + l q.1)) (p, x)‖ ≤ C := by
  obtain ⟨N, C₀, hC₀, hN⟩ := hA.norm_iteratedFDeriv_le_uniform n
  set L : P × E →L[ℝ] E := ContinuousLinearMap.snd ℝ P E + l ∘L ContinuousLinearMap.fst ℝ P E with hL
  have hLq : ∀ q : P × E, L q = q.2 + l q.1 := fun q => rfl
  set c : ℝ := 1 + (‖z‖ + 1) + ‖l‖ * (‖z‖ + 1) with hc
  set S : ℝ := 2 ^ (k + N) * ((Finset.Iic (k + N, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) s with hS
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C₀ * c ^ (k + N) * ‖L‖ ^ (n - i) * S,
    fun p hp x => ?_⟩
  have hp' : ‖p‖ ≤ ‖z‖ + 1 := by
    have := norm_add_le z (p - z)
    rw [add_sub_cancel] at this
    linarith
  have hx : ‖x‖ ≤ ‖x + l p‖ + ‖l‖ * (‖z‖ + 1) := by
    have h1 := norm_sub_le (x + l p) (l p)
    rw [add_sub_cancel_right] at h1
    have h2 : ‖l p‖ ≤ ‖l‖ * (‖z‖ + 1) := (l.le_opNorm p).trans (by gcongr)
    linarith
  have hl0 : 0 ≤ ‖l‖ * (‖z‖ + 1) := by positivity
  have hq : 1 + ‖(p, x)‖ ≤ c * (1 + ‖x + l p‖) := by
    have h1 : ‖(p, x)‖ ≤ ‖p‖ + ‖x‖ := by
      rw [Prod.norm_def]
      exact max_le (by simp) (by simp)
    have h2 : 1 * ‖x + l p‖ ≤ c * ‖x + l p‖ := by
      gcongr
      have := norm_nonneg z
      linarith
    linarith
  have hx' : ‖x‖ ≤ c * (1 + ‖x + l p‖) := by
    have := norm_snd_le (p, x)
    linarith
  have hs : ContDiff ℝ ∞ (⇑s ∘ L) := (s.smooth ⊤).comp L.contDiff
  have h1 := norm_iteratedFDeriv_mul_le hA.1 hs (p, x) (n := n) (by norm_cast; simp)
  refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
  have h2 : ‖iteratedFDeriv ℝ (n - i) (⇑s ∘ L) (p, x)‖ ≤
      ‖iteratedFDeriv ℝ (n - i) s (x + l p)‖ * ‖L‖ ^ (n - i) := by
    rw [L.iteratedFDeriv_comp_right (s.smooth ⊤) _ (by generalize n - i = j; exact_mod_cast le_top)]
    simpa [hLq] using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ (n - i) s (L (p, x))) (fun _ => L)
  have h3 : (1 + ‖x + l p‖) ^ (k + N) * ‖iteratedFDeriv ℝ (n - i) s (x + l p)‖ ≤ S :=
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + N, n)) le_rfl (Nat.sub_le _ _) s _
  have h4 := hN i hi' (p, x)
  have hc0 : 0 ≤ c := by positivity
  calc _ ≤ (c * (1 + ‖x + l p‖)) ^ k * ((n.choose i : ℝ) * (C₀ * (c * (1 + ‖x + l p‖)) ^ N) *
        (‖iteratedFDeriv ℝ (n - i) s (x + l p)‖ * ‖L‖ ^ (n - i))) := by
        gcongr
        exact h4.trans (by gcongr)
    _ = (n.choose i : ℝ) * C₀ * c ^ (k + N) * ‖L‖ ^ (n - i) *
        ((1 + ‖x + l p‖) ^ (k + N) * ‖iteratedFDeriv ℝ (n - i) s (x + l p)‖) := by
        simp only [mul_pow, pow_add]; ring
    _ ≤ _ := by gcongr

end family

theorem temperate_exp : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by
  have hd : ∀ n : ℕ, iteratedDeriv n (fun t : ℝ => cexp (I * t)) = fun t : ℝ => I ^ n * cexp (I * t) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have : HasDerivAt (fun t : ℝ => I ^ n * cexp (I * t)) (I ^ n * (cexp (I * t) * (I * 1))) t :=
        (((hasDerivAt_id (t : ℂ)).const_mul I).cexp.const_mul _).comp_ofReal
      rw [this.deriv]; ring
  refine ⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff),
    fun n => ⟨0, 1, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]
  simp

variable {κ : Type} [Fintype κ]

noncomputable def dotL (κ : Type) [Fintype κ] : (κ → ℝ) →L[ℝ] (κ → ℝ) →L[ℝ] ℝ :=
  ∑ i : κ, (ContinuousLinearMap.proj i : (κ → ℝ) →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj i : (κ → ℝ) →L[ℝ] ℝ)

noncomputable def phase (q : W κ ℝ × (κ → ℝ)) : ℝ :=
  2 * Real.pi * dotL κ q.2 q.1.2 + Real.pi * dotL κ q.1.1 q.1.2

noncomputable def ker (s : (κ → ℝ) → ℂ) (q : W κ ℝ × (κ → ℝ)) : ℂ :=
  cexp (I * (phase q : ℝ)) * s (q.2 + q.1.1)

end GlobalTheory.CompanionTheory.OM.SchDiff

namespace GlobalTheory.CompanionTheory.OM

open SchDiff

end GlobalTheory.CompanionTheory.OM

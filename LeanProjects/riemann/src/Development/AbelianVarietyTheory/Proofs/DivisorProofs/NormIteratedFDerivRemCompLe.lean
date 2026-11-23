import Mathlib

open Complex

namespace GlobalTheory.CharFormDeriv

theorem iteratedDeriv_const_mul_cexp (a c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => c * Complex.exp (a * y)) =
      fun y : ℝ => c * a ^ n * Complex.exp (a * y) := by
  induction n generalizing c with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y : ℝ => c * Complex.exp (a * y)) =
        fun y : ℝ => (c * a) * Complex.exp (a * y) := by
      funext y
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
        simpa using (hasDerivAt_id y).ofReal_comp
      have h : HasDerivAt (fun y : ℝ => c * Complex.exp (a * y))
          (c * (Complex.exp (a * y) * (a * 1))) y :=
        ((h1.const_mul a).cexp).const_mul c
      rw [h.deriv]; ring
    rw [hd, ih]; funext y; ring

theorem deriv_affine_cexp (a c d e : ℂ) :
    deriv (fun y : ℝ => c * Complex.exp (a * y) + d * y + e) =
      fun y : ℝ => c * a * Complex.exp (a * y) + d := by
  funext y
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have h : HasDerivAt (fun y : ℝ => c * Complex.exp (a * y) + d * y + e)
      (c * (Complex.exp (a * y) * (a * 1)) + d * 1) y :=
    ((((h1.const_mul a).cexp).const_mul c).add (h1.const_mul d)).add_const e
  rw [h.deriv]; ring

theorem norm_cexp_mul_I_sub_one_le (z : ℝ) : ‖Complex.exp (z * I) - 1‖ ≤ 2 * |z| := by
  rcases le_or_gt |z| 1 with hz | hz
  · have hn : ‖(z : ℂ) * I‖ = |z| := by simp
    have := Complex.norm_exp_sub_one_le (x := (z : ℂ) * I) (by rw [hn]; exact hz)
    rwa [hn] at this
  · calc ‖Complex.exp (z * I) - 1‖ ≤ ‖Complex.exp (z * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I]; norm_num
      _ ≤ 2 * |z| := by linarith

theorem norm_cexp_mul_I_sub_one_sub_le (z : ℝ) :
    ‖Complex.exp (z * I) - 1 - z * I‖ ≤ 3 * z ^ 2 := by
  have hn : ‖(z : ℂ) * I‖ = |z| := by simp
  rcases le_or_gt |z| 1 with hz | hz
  · have := Complex.norm_exp_sub_one_sub_id_le (x := (z : ℂ) * I) (by rw [hn]; exact hz)
    rw [hn, sq_abs] at this
    nlinarith [sq_nonneg z]
  · calc ‖Complex.exp (z * I) - 1 - z * I‖
        ≤ ‖Complex.exp (z * I)‖ + ‖(1 : ℂ)‖ + ‖(z : ℂ) * I‖ := norm_sub_le_of_le (norm_sub_le _ _) le_rfl
      _ = 2 + |z| := by rw [Complex.norm_exp_ofReal_mul_I, hn]; norm_num
      _ ≤ 3 * z ^ 2 := by
        have : |z| ^ 2 = z ^ 2 := sq_abs z
        nlinarith

end GlobalTheory.CharFormDeriv

namespace GlobalTheory.CharFormDeriv

noncomputable def rem (t : ℝ) (y : ℝ) : ℂ :=
  (t : ℂ)⁻¹ * Complex.exp ((I * t) * y) + (-I) * y + (-(t : ℂ)⁻¹)

theorem rem_eq {t : ℝ} (ht0 : t ≠ 0) (y : ℝ) :
    rem t y = (t : ℂ)⁻¹ * (Complex.exp (((t * y : ℝ) : ℂ) * I) - 1 - ((t * y : ℝ) : ℂ) * I) := by
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  simp only [rem]
  push_cast
  field_simp
  ring_nf

theorem norm_iteratedDeriv_rem_le {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) (i : ℕ) (y : ℝ) :
    ‖iteratedDeriv i (rem t) y‖ ≤ 3 * |t| * (1 + |y|) ^ 2 := by
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  have habs : 0 < |t| := abs_pos.mpr ht0
  have hy : 0 ≤ |y| := abs_nonneg y
  have hexp : (I * t) * (y : ℂ) = ((t * y : ℝ) : ℂ) * I := by push_cast; ring
  have hnexp : ‖Complex.exp ((I * t) * (y : ℂ))‖ = 1 := by
    rw [hexp, Complex.norm_exp_ofReal_mul_I]
  have hy1 : y ^ 2 ≤ (1 + |y|) ^ 2 := by
    rw [← sq_abs y]; nlinarith
  have hy2 : |y| ≤ (1 + |y|) ^ 2 := by nlinarith
  have hrem : rem t = fun y : ℝ => (t : ℂ)⁻¹ * Complex.exp ((I * t) * y) + (-I) * y + (-(t : ℂ)⁻¹) := rfl
  have hd1 : deriv (rem t) = fun y : ℝ => (t : ℂ)⁻¹ * (I * t) * Complex.exp ((I * t) * y) + (-I) := by
    rw [hrem, deriv_affine_cexp]
  match i with
  | 0 =>
    rw [iteratedDeriv_zero, rem_eq ht0, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    have h3 := norm_cexp_mul_I_sub_one_sub_le (t * y)
    calc |t|⁻¹ * ‖Complex.exp (((t * y : ℝ) : ℂ) * I) - 1 - ((t * y : ℝ) : ℂ) * I‖
        ≤ |t|⁻¹ * (3 * (t * y) ^ 2) := by gcongr
      _ = 3 * |t| * y ^ 2 := by
        rw [mul_pow, ← sq_abs t]; field_simp
      _ ≤ 3 * |t| * (1 + |y|) ^ 2 := by gcongr
  | 1 =>
    rw [iteratedDeriv_one, hd1]
    simp only
    have e : (t : ℂ)⁻¹ * (I * t) * Complex.exp ((I * t) * y) + (-I)
        = I * (Complex.exp (((t * y : ℝ) : ℂ) * I) - 1) := by
      rw [hexp]; field_simp; ring
    rw [e, norm_mul, Complex.norm_I, one_mul]
    calc ‖Complex.exp (((t * y : ℝ) : ℂ) * I) - 1‖ ≤ 2 * |t * y| := norm_cexp_mul_I_sub_one_le _
      _ = 2 * |t| * |y| := by rw [abs_mul]; ring
      _ ≤ 3 * |t| * (1 + |y|) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hy2 habs.le
        nlinarith
  | m + 2 =>
    have hd1' : deriv (rem t) = fun y : ℝ =>
        ((t : ℂ)⁻¹ * (I * t)) * Complex.exp ((I * t) * y) + 0 * y + (-I) := by
      rw [hd1]; funext y; ring
    have hd2 : deriv (deriv (rem t)) = fun y : ℝ =>
        ((t : ℂ)⁻¹ * (I * t) * (I * t)) * Complex.exp ((I * t) * y) := by
      rw [hd1', deriv_affine_cexp]; funext y; ring
    rw [iteratedDeriv_succ', iteratedDeriv_succ', hd2, iteratedDeriv_const_mul_cexp]
    simp only
    rw [norm_mul, hnexp, mul_one]
    simp only [norm_mul, norm_pow, norm_inv, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    have hp : |t| ^ m ≤ 1 := pow_le_one₀ habs.le ht1
    calc |t|⁻¹ * |t| * |t| * |t| ^ m = |t| * |t| ^ m := by field_simp
      _ ≤ |t| * 1 := by gcongr
      _ ≤ 3 * |t| * (1 + |y|) ^ 2 := by
        have : 1 ≤ (1 + |y|) ^ 2 := by nlinarith
        nlinarith

end GlobalTheory.CharFormDeriv

namespace GlobalTheory.CharFormDeriv

theorem contDiff_rem (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (rem t) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  unfold rem; fun_prop

theorem norm_iteratedFDeriv_rem_comp_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (fun x => rem t (L x)) x‖ ≤ 3 * |t| * (1 + ‖L‖ * ‖x‖) ^ 2 * ‖L‖ ^ i := by
  have h := L.iteratedFDeriv_comp_right (contDiff_rem t) x (i := i) (by exact_mod_cast le_top)
  have e : (fun x => rem t (L x)) = rem t ∘ ⇑L := rfl
  rw [e, h]
  calc _ ≤ ‖iteratedFDeriv ℝ i (rem t) (L x)‖ * ∏ _j : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedDeriv i (rem t) (L x)‖ * ‖L‖ ^ i := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; simp
    _ ≤ 3 * |t| * (1 + |L x|) ^ 2 * ‖L‖ ^ i := by
        gcongr; exact norm_iteratedDeriv_rem_le ht0 ht1 i (L x)
    _ ≤ 3 * |t| * (1 + ‖L‖ * ‖x‖) ^ 2 * ‖L‖ ^ i := by
        gcongr; rw [← Real.norm_eq_abs]; exact L.le_opNorm x

theorem hasTemperateGrowth_char {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (t : ℝ) :
    Function.HasTemperateGrowth (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) := by
    fun_prop
  have e : (fun x : V => Complex.exp ((I * t) * (L x : ℂ)))
      = (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) ∘ ⇑L := by
    funext x; simp
  refine ⟨by rw [e]; exact hc.comp L.contDiff, fun n => ⟨0, (|t| * ‖L‖) ^ n, fun x => ?_⟩⟩
  rw [e, L.iteratedFDeriv_comp_right hc x (i := n) (by exact_mod_cast le_top), pow_zero, mul_one]
  calc _ ≤ ‖iteratedFDeriv ℝ n (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) (L x)‖
          * ∏ _j : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (|t| * ‖L‖) ^ n := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const_mul_cexp]
        have hexp : (I * t) * ((L x : ℝ) : ℂ) = ((t * L x : ℝ) : ℂ) * I := by push_cast; ring
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_mul, norm_pow, norm_mul,
          Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        simp [mul_pow]

end GlobalTheory.CharFormDeriv

namespace GlobalTheory.CharFormDeriv

theorem seminorm_rem_mul_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (f u : SchwartzMap V ℂ) {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1)
    (hu : ∀ x, u x = rem t (L x) * f x) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n u ≤ |t| * (3 * 2 ^ n * (1 + ‖L‖) ^ (n + 2) *
      (2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)) := by
  set S := 2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f
    with hS
  have hS0 : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg L
  refine SchwartzMap.seminorm_le_bound ℂ k n u (by positivity) fun x => ?_
  have hu' : (⇑u) = fun x => rem t (L x) * f x := funext hu
  rw [hu']
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((contDiff_rem t).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ (n.choose i : ℝ) * (|t| * (3 * (1 + ‖L‖) ^ (n + 2) * S)) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ ≤ 3 * |t| * (1 + ‖L‖ * ‖x‖) ^ 2 * ‖L‖ ^ i :=
      norm_iteratedFDeriv_rem_comp_le L ht0 ht1 i x
    have h2 : (1 + ‖x‖) ^ (k + 2) * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ S :=
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + 2, n)) le_rfl (Nat.sub_le n i) f x
    have h3 : (1 + ‖L‖ * ‖x‖) ^ 2 ≤ (1 + ‖L‖) ^ 2 * (1 + ‖x‖) ^ 2 := by
      rw [← mul_pow]; gcongr; nlinarith
    have h4 : ‖L‖ ^ i ≤ (1 + ‖L‖) ^ n :=
      calc ‖L‖ ^ i ≤ (1 + ‖L‖) ^ i := by gcongr; linarith
        _ ≤ (1 + ‖L‖) ^ n := pow_le_pow_right₀ (by linarith) hi'
    have h5 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
    have hA : ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖
        ≤ 3 * |t| * ((1 + ‖L‖) ^ 2 * (1 + ‖x‖) ^ 2) * (1 + ‖L‖) ^ n :=
      h1.trans (by gcongr)
    have hc0 : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        = (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ (n.choose i : ℝ) * ((1 + ‖x‖) ^ k *
          (3 * |t| * ((1 + ‖L‖) ^ 2 * (1 + ‖x‖) ^ 2) * (1 + ‖L‖) ^ n) *
          ‖iteratedFDeriv ℝ (n - i) f x‖) := by gcongr
      _ = (n.choose i : ℝ) * (|t| * (3 * (1 + ‖L‖) ^ (n + 2) *
          ((1 + ‖x‖) ^ (k + 2) * ‖iteratedFDeriv ℝ (n - i) f x‖))) := by ring
      _ ≤ (n.choose i : ℝ) * (|t| * (3 * (1 + ‖L‖) ^ (n + 2) * S)) := by gcongr
  have hfun : (fun x => rem t (L x) * f x) = fun y => (rem t ∘ ⇑L) y * f y := rfl
  rw [hfun]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => (rem t ∘ ⇑L) y * f y) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (|t| * (3 * (1 + ‖L‖) ^ (n + 2) * S)) :=
        Finset.sum_le_sum hterm
    _ = |t| * (3 * 2 ^ n * (1 + ‖L‖) ^ (n + 2) * S) := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this]; ring

end GlobalTheory.CharFormDeriv

namespace GlobalTheory.CharFormDeriv

theorem charForm_kills_linear_mul : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (T : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (f g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * f x) → T g = 0 := by
  intro V _ _ _ T hT L f g hg
  let ft : ℝ → SchwartzMap V ℂ := fun t =>
    SchwartzMap.smulLeftCLM ℂ (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) f
  have hft : ∀ t x, ft t x = Complex.exp ((I * t) * (L x : ℂ)) * f x := fun t x => by
    simp only [ft, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_char L t), smul_eq_mul]
  have hTft : ∀ t : ℝ, T (ft t) = T f := fun t => hT (t • L) f (ft t) (fun x => by
    rw [hft, ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc])
  let u : ℝ → SchwartzMap V ℂ := fun t => (t : ℂ)⁻¹ • (ft t - f) - I • g
  have hu : ∀ t : ℝ, ∀ x, u t x = rem t (L x) * f x := fun t x => by
    simp only [u, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hft, hg, rem, smul_eq_mul]
    ring
  have hTu : ∀ t : ℝ, T (u t) = -I * T g := fun t => by
    simp only [u, map_sub, map_smul, hTft, sub_self, smul_zero, smul_eq_mul, zero_sub]
    ring
  have hlim : Filter.Tendsto u (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    rw [(schwartz_withSeminorms ℂ V ℂ).tendsto_nhds u 0]
    rintro ⟨k, n⟩ ε hε
    set K := 3 * 2 ^ n * (1 + ‖L‖) ^ (n + 2) *
      (2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)
      with hK
    have hK0 : 0 ≤ K := mul_nonneg (by positivity) (mul_nonneg (by positivity) (apply_nonneg _ _))
    have hδ : 0 < min 1 (ε / (K + 1)) := lt_min one_pos (div_pos hε (by linarith))
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ), self_mem_nhdsWithin]
      with t ht ht0
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    have ht0' : t ≠ 0 := ht0
    have ht1 : |t| ≤ 1 := (lt_of_lt_of_le ht (min_le_left _ _)).le
    have htε : |t| < ε / (K + 1) := lt_of_lt_of_le ht (min_le_right _ _)
    rw [sub_zero]
    show SchwartzMap.seminorm ℂ k n (u t) < ε
    calc SchwartzMap.seminorm ℂ k n (u t) ≤ |t| * K := seminorm_rem_mul_le L f (u t) ht0' ht1 (hu t) k n
      _ ≤ |t| * (K + 1) := by gcongr; linarith
      _ < ε / (K + 1) * (K + 1) := by gcongr
      _ = ε := by field_simp
  have hcont : Filter.Tendsto (fun t => T (u t)) (nhdsWithin 0 {0}ᶜ) (nhds (T 0)) :=
    (T.continuous.tendsto 0).comp hlim
  have hconst : Filter.Tendsto (fun t => T (u t)) (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (-I * T g)) := by
    simp only [hTu]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hconst hcont
  rw [map_zero, neg_mul, neg_eq_zero] at heq
  exact (mul_eq_zero.mp heq).resolve_left Complex.I_ne_zero

end GlobalTheory.CharFormDeriv

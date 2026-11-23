import Mathlib

open scoped ContDiff

namespace GlobalTheory.ExpDivision

theorem hasTemperateGrowth_of_closed (S : Set (ℝ → ℂ))
    (hd : ∀ f ∈ S, Differentiable ℝ f) (hc : ∀ f ∈ S, deriv f ∈ S)
    (hb : ∀ f ∈ S, ∃ (k : ℕ) (C : ℝ), ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k)
    {f : ℝ → ℂ} (hf : f ∈ S) : f.HasTemperateGrowth := by
  have hi : ∀ n, iteratedDeriv n f ∈ S := by
    intro n
    induction n with
    | zero => simpa using hf
    | succ n ih => rw [iteratedDeriv_succ]; exact hc _ ih
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => hd _ (hi m), fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hb _ (hi n)
  exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact h x⟩

theorem hasTemperateGrowth_deriv {f : ℝ → ℂ} (hf : f.HasTemperateGrowth) :
    (deriv f).HasTemperateGrowth := by
  refine ⟨(contDiff_infty_iff_deriv.1 hf.1).2, fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  refine ⟨k, C, fun x => ?_⟩
  have := h x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at this ⊢
  rwa [iteratedDeriv_succ'] at this

theorem hasTemperateGrowth_div {E g : ℝ → ℂ} (hE : E.HasTemperateGrowth)
    (h0 : ∀ x, E x ≠ 0) {N : ℕ} {M : ℝ} (hM : ∀ x, ‖(E x)⁻¹‖ ≤ M * (1 + ‖x‖) ^ N)
    (hg : g.HasTemperateGrowth) : (fun x => g x / E x).HasTemperateGrowth := by
  have hEd : Differentiable ℝ E := hE.1.differentiable (by simp)
  refine hasTemperateGrowth_of_closed
    {f | ∃ (m : ℕ) (u : ℝ → ℂ), u.HasTemperateGrowth ∧ f = fun x => u x / E x ^ m} ?_ ?_ ?_
    ⟨1, g, hg, by simp⟩
  · rintro f ⟨m, u, hu, rfl⟩
    have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
    exact hud.div (hEd.pow m) fun x => pow_ne_zero _ (h0 x)
  · rintro f ⟨m, u, hu, rfl⟩
    have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
    have hp : (fun x => E x ^ m).HasTemperateGrowth := hE.pow m
    have hpd : Differentiable ℝ (fun x => E x ^ m) := hp.1.differentiable (by simp)
    refine ⟨m * 2, fun x => deriv u x * E x ^ m - u x * deriv (fun x => E x ^ m) x,
      ((hasTemperateGrowth_deriv hu).mul hp).sub (hu.mul (hasTemperateGrowth_deriv hp)), ?_⟩
    funext x
    rw [pow_mul]
    exact deriv_fun_div (hud x) (hpd x) (pow_ne_zero _ (h0 x))
  · rintro f ⟨m, u, hu, rfl⟩
    obtain ⟨k, C, h⟩ := hu.2 0
    refine ⟨k + N * m, C * M ^ m, fun x => ?_⟩
    have h1 : ‖u x‖ ≤ C * (1 + ‖x‖) ^ k := by simpa using h x
    have h2 := hM x
    have h3 : 0 ≤ C * (1 + ‖x‖) ^ k := (norm_nonneg _).trans h1
    calc ‖u x / E x ^ m‖ = ‖u x‖ * ‖(E x)⁻¹‖ ^ m := by
          rw [div_eq_mul_inv, norm_mul, ← inv_pow, norm_pow]
      _ ≤ (C * (1 + ‖x‖) ^ k) * (M * (1 + ‖x‖) ^ N) ^ m := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

theorem hasTemperateGrowth_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ R → ‖F z‖ ≤ C) :
    (fun t : ℝ => F t).HasTemperateGrowth := by
  refine hasTemperateGrowth_of_closed
    {f | ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ R → ‖G z‖ ≤ C) ∧
      f = fun t : ℝ => G t} ?_ ?_ ?_ ⟨F, hF, hb, rfl⟩
  · rintro f ⟨G, hG, -, rfl⟩ x
    exact (hG x).hasDerivAt.comp_ofReal.differentiableAt
  · rintro f ⟨G, hG, hB, rfl⟩
    refine ⟨deriv G, hG.deriv, fun R => ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hB (R + 1)
      refine ⟨C / 1, fun z hz => ?_⟩
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hG.diffContOnCl ?_
      intro w hw
      apply hC
      have h1 : ‖w - z‖ = 1 := by simpa [dist_eq_norm] using hw
      have h2 := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im, h1] at h2
      have h3 := abs_add_le (w.im - z.im) z.im
      rw [sub_add_cancel] at h3
      linarith
    · funext x
      exact (hG x).hasDerivAt.comp_ofReal.deriv
  · rintro f ⟨G, -, hB, rfl⟩
    obtain ⟨C, hC⟩ := hB 0
    exact ⟨0, C, fun x => by simpa using hC x (by simp)⟩

noncomputable def quot (a : ℝ) : ℂ → ℂ := dslope (fun z => Complex.exp (Complex.I * (a * z))) 0

theorem mul_quot (a : ℝ) (z : ℂ) : z * quot a z = Complex.exp (Complex.I * (a * z)) - 1 := by
  have := sub_smul_dslope (fun z : ℂ => Complex.exp (Complex.I * (a * z))) 0 z
  simpa [quot] using this

theorem quot_zero (a : ℝ) : quot a 0 = Complex.I * a := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * (a * z)))
      (Complex.exp (Complex.I * (a * 0)) * (Complex.I * (a * 1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).const_mul (a : ℂ)).const_mul Complex.I).cexp
  rw [quot, dslope_same, h.deriv]; simp

theorem differentiable_quot (a : ℝ) : Differentiable ℂ (quot a) := by
  rw [← differentiableOn_univ, quot, Complex.differentiableOn_dslope Filter.univ_mem]
  fun_prop

theorem hasTemperateGrowth_quot (a : ℝ) : (fun t : ℝ => quot a t).HasTemperateGrowth := by
  refine hasTemperateGrowth_of_entire (differentiable_quot a) fun R => ?_
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (differentiable_quot a).continuous.continuousOn
  refine ⟨max C (Real.exp (|a| * R) + 1), fun z hz => ?_⟩
  by_cases h : ‖z‖ ≤ 1
  · exact (hC z (by simpa using h)).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    push Not at h
    have h1 : ‖z‖ * ‖quot a z‖ ≤ Real.exp (|a| * R) + 1 := by
      rw [← norm_mul, mul_quot]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_exp, norm_one]
      gcongr
      have : (Complex.I * (a * z)).re = -(a * z.im) := by simp
      rw [this]
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]
      gcongr
    nlinarith [norm_nonneg (quot a z)]

theorem quot_neg (a t : ℝ) : quot (-a) t = (starRingEnd ℂ) (quot a t) := by
  by_cases ht : t = 0
  · subst ht; simp [quot_zero]
  · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    apply mul_left_cancel₀ ht'
    have := congrArg (starRingEnd ℂ) (mul_quot a t)
    rw [map_mul, Complex.conj_ofReal] at this
    rw [this, mul_quot, map_sub, ← Complex.exp_conj]
    simp

theorem norm_exp_sub_one_ge (x : ℝ) :
    4 * |x - round x| ≤ ‖Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖ := by
  have h1 : Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * (x - round x) : ℝ) : ℂ)) := by
    have : Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) =
        Complex.I * ((2 * Real.pi * (x - round x) : ℝ) : ℂ) + (round x : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h2 := abs_sub_round x
  set d := x - round x
  have hp := Real.pi_pos
  have e : 2 * Real.pi * d / 2 = Real.pi * d := by ring
  have h3 : |Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hp]; nlinarith
  have h4 := Real.mul_abs_le_abs_sin h3
  rw [abs_mul, abs_of_pos hp] at h4
  have e2 : 2 / Real.pi * (Real.pi * |d|) = 2 * |d| := by field_simp
  rw [e2] at h4
  rw [e, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  linarith

theorem dioph (t : ℝ) (hp : round t ≠ 0) :
    1 ≤ 6 * (1 + |t|) * (|t - round t| + |√2 * t - round (√2 * t)|) := by
  set p := round t with hpdef
  set q := round (√2 * t) with hqdef
  have h1 : |t - p| ≤ 1 / 2 := abs_sub_round t
  have h2 : |√2 * t - q| ≤ 1 / 2 := abs_sub_round _
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hs2 : √2 ≤ 3 / 2 := by nlinarith
  have hne : (2 * p ^ 2 - q ^ 2 : ℤ) ≠ 0 := by
    intro h
    have hr : (2 : ℝ) * p ^ 2 - q ^ 2 = 0 := by exact_mod_cast h
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    have : (√2 * p - q) * (√2 * p + q) = 0 := by nlinarith
    have hirr := irrational_sqrt_two
    rcases mul_eq_zero.1 this with h' | h'
    · exact hirr ⟨(q : ℚ) / p, by push_cast; field_simp; linarith⟩
    · exact hirr ⟨-(q : ℚ) / p, by push_cast; field_simp; linarith⟩
  have h3 : (1 : ℝ) ≤ |(2 : ℝ) * p ^ 2 - q ^ 2| := by
    have := Int.one_le_abs hne
    exact_mod_cast this
  have h4 : (2 : ℝ) * p ^ 2 - q ^ 2 = (√2 * p - q) * (√2 * p + q) := by nlinarith
  rw [h4, abs_mul] at h3
  have h5 : |√2 * p - q| ≤ 2 * (|t - p| + |√2 * t - q|) := by
    have : √2 * p - q = (√2 * t - q) - √2 * (t - p) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos hs0]
    nlinarith [abs_nonneg (t - p), abs_nonneg (√2 * t - q)]
  have h6 : |√2 * p + q| ≤ 3 * (1 + |t|) := by
    have : √2 * p + q = 2 * √2 * t - (√2 * t - q) - √2 * (t - p) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    have := abs_sub (2 * √2 * t) (√2 * t - q)
    rw [abs_mul, abs_mul, abs_of_pos hs0, abs_two] at this
    rw [abs_mul, abs_of_pos hs0]
    nlinarith [abs_nonneg (t - p), abs_nonneg t]
  calc (1 : ℝ) ≤ _ := h3
    _ ≤ (2 * (|t - p| + |√2 * t - q|)) * (3 * (1 + |t|)) := by gcongr
    _ = _ := by ring

theorem lower (t : ℝ) :
    1 ≤ 2 * (1 + |t|) ^ 2 * (‖quot (2 * Real.pi) t‖ + ‖quot (2 * Real.pi * √2) t‖) := by
  have a0 := abs_nonneg t
  have n1 := norm_nonneg (quot (2 * Real.pi) t)
  have n2 := norm_nonneg (quot (2 * Real.pi * √2) t)
  have e1 : 4 * |t - round t| ≤ |t| * ‖quot (2 * Real.pi) t‖ := by
    have := norm_exp_sub_one_ge t
    rwa [Complex.ofReal_mul _ t, ← mul_quot, norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
  have e2 : 4 * |√2 * t - round (√2 * t)| ≤ |t| * ‖quot (2 * Real.pi * √2) t‖ := by
    have := norm_exp_sub_one_ge (√2 * t)
    rwa [← mul_assoc, Complex.ofReal_mul _ t, ← mul_quot, norm_mul, Complex.norm_real,
      Real.norm_eq_abs] at this
  by_cases hp : round t = 0
  · have h1 : 1 ≤ ‖quot (2 * Real.pi) t‖ := by
      by_cases ht : t = 0
      · subst ht
        rw [Complex.ofReal_zero, quot_zero, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith [Real.pi_gt_three]
      · rw [hp] at e1
        simp only [Int.cast_zero, sub_zero] at e1
        have : 0 < |t| := abs_pos.2 ht
        by_contra hh
        nlinarith
    have h2 : 1 ≤ (1 + |t|) ^ 2 := by nlinarith
    nlinarith
  · have h := dioph t hp
    set s := ‖quot (2 * Real.pi) t‖ + ‖quot (2 * Real.pi * √2) t‖ with hs
    have hs0 : 0 ≤ s := by positivity
    have h1 : 4 * (|t - round t| + |√2 * t - round (√2 * t)|) ≤ (1 + |t|) * s := by
      rw [hs]; nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 + |t| by positivity)
    have h3 : 0 ≤ (1 + |t|) ^ 2 * s := by positivity
    nlinarith

theorem exists_division : ∃ (n : ℕ) (a : Fin n → ℝ) (A : Fin n → ℝ → ℂ),
    (∀ j, Function.HasTemperateGrowth (A j)) ∧
    ∀ t : ℝ, (t : ℂ) = ∑ j, (Complex.exp (Complex.I * ((a j * t : ℝ) : ℂ)) - 1) * A j t := by
  set a : ℝ := 2 * Real.pi with ha
  set b : ℝ := 2 * Real.pi * √2 with hb
  set E : ℝ → ℂ := fun t => quot a t * quot (-a) t + quot b t * quot (-b) t with hE
  have hEt : E.HasTemperateGrowth :=
    ((hasTemperateGrowth_quot a).mul (hasTemperateGrowth_quot (-a))).add
      ((hasTemperateGrowth_quot b).mul (hasTemperateGrowth_quot (-b)))
  have hn : ∀ t, ‖E t‖ = ‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2 := by
    intro t
    have : E t = ((‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2 : ℝ) : ℂ) := by
      simp only [hE, quot_neg, Complex.mul_conj']
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hl : ∀ t, 1 ≤ 8 * (1 + ‖t‖) ^ 4 * ‖E t‖ := by
    intro t
    have h := lower t
    rw [← ha, ← hb] at h
    rw [hn, Real.norm_eq_abs]
    have h2 := one_le_pow₀ (n := 2) h
    have h3 : (‖quot a t‖ + ‖quot b t‖) ^ 2 ≤ 2 * (‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2) := by
      nlinarith [sq_nonneg (‖quot a t‖ - ‖quot b t‖)]
    calc (1 : ℝ) ≤ _ := h2
      _ = 4 * (1 + |t|) ^ 4 * (‖quot a t‖ + ‖quot b t‖) ^ 2 := by ring
      _ ≤ 4 * (1 + |t|) ^ 4 * (2 * (‖quot a t‖ ^ 2 + ‖quot b t‖ ^ 2)) := by gcongr
      _ = _ := by ring
  have h0 : ∀ t, E t ≠ 0 := by
    intro t h
    have := hl t
    rw [h] at this
    norm_num at this
  have hM : ∀ t, ‖(E t)⁻¹‖ ≤ 8 * (1 + ‖t‖) ^ 4 := by
    intro t
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.2 (h0 t))]
    exact hl t
  refine ⟨2, ![a, b], ![fun t => quot (-a) t / E t, fun t => quot (-b) t / E t], ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hasTemperateGrowth_div hEt h0 hM (hasTemperateGrowth_quot _)
    · exact hasTemperateGrowth_div hEt h0 hM (hasTemperateGrowth_quot _)
  · intro t
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Complex.ofReal_mul a t, Complex.ofReal_mul b t, ← mul_quot, ← mul_quot]
    have := h0 t
    field_simp
    simp only [hE]

end GlobalTheory.ExpDivision

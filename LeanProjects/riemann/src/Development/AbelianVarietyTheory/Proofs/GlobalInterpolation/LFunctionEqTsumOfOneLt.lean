import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.DirichletTail

open Filter Topology

theorem norm_sum_range_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (m : ℕ) :
    ‖∑ n ∈ Finset.range m, χ ((n + 1 : ℕ) : ZMod q)‖ ≤ q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hper : ∑ a : ZMod q, χ a = ∑ n ∈ Finset.range q, χ (n : ZMod q) := by
    refine Finset.sum_bij' (fun a _ ↦ a.val) (fun n _ ↦ (n : ZMod q)) ?_ ?_ ?_ ?_ ?_
    · intro a _
      exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro n _
      exact Finset.mem_univ _
    · intro a _
      exact ZMod.natCast_zmod_val a
    · intro n hn
      exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)
    · intro a _
      rw [ZMod.natCast_zmod_val]
  have hshift : ∀ k : ℕ, ∑ n ∈ Finset.range q, χ ((k + n : ℕ) : ZMod q) = 0 := by
    intro k
    induction k with
    | zero =>
      simp only [zero_add]
      rw [← hper]
      exact MulChar.sum_eq_zero_of_ne_one hχ
    | succ k ih =>
      have h1 := Finset.sum_range_succ (fun n ↦ χ ((k + n : ℕ) : ZMod q)) q
      have h2 := Finset.sum_range_succ' (fun n ↦ χ ((k + n : ℕ) : ZMod q)) q
      beta_reduce at h1 h2
      have hkq : χ ((k + q : ℕ) : ZMod q) = χ ((k + 0 : ℕ) : ZMod q) := by
        simp [Nat.cast_add]
      have hc : ∑ n ∈ Finset.range q, χ ((k + 1 + n : ℕ) : ZMod q) =
          ∑ n ∈ Finset.range q, χ ((k + (n + 1) : ℕ) : ZMod q) :=
        Finset.sum_congr rfl fun n _ ↦ by rw [show k + 1 + n = k + (n + 1) by omega]
      rw [hc]
      linear_combination ih + hkq - h1.symm.trans h2
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m ≤ q
    · calc ‖∑ n ∈ Finset.range m, χ ((n + 1 : ℕ) : ZMod q)‖
          ≤ ∑ n ∈ Finset.range m, ‖χ ((n + 1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.range m, (1 : ℝ) := Finset.sum_le_sum fun n _ ↦ χ.norm_le_one _
        _ = m := by simp
        _ ≤ q := by exact_mod_cast hm
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + q := ⟨m - q, by omega⟩
      rw [Finset.sum_range_add]
      have hb : ∑ x ∈ Finset.range q, χ ((k + x + 1 : ℕ) : ZMod q) = 0 := by
        rw [← hshift (k + 1)]
        exact Finset.sum_congr rfl fun x _ ↦ by rw [show k + x + 1 = k + 1 + x by omega]
      rw [hb, add_zero]
      exact ih k (by omega)

theorem norm_cpow_sub_le {a b δ : ℝ} {s : ℂ} (ha : 1 ≤ a) (hab : a ≤ b) (hδ : 0 < δ)
    (hs : δ ≤ s.re) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ / δ * (a ^ (-δ) - b ^ (-δ)) := by
  have hσ : 0 < s.re := lt_of_lt_of_le hδ hs
  have hs0 : -s ≠ 0 := by
    intro h
    rw [neg_eq_zero.mp h, Complex.zero_re] at hσ
    exact lt_irrefl _ hσ
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht ↦ lt_of_lt_of_le one_pos (ha.trans ht.1)
  have hf : ∀ t ∈ Set.Icc a b, HasDerivAt (fun x : ℝ ↦ (a : ℂ) ^ (-s) - (x : ℂ) ^ (-s))
      (-(-s * (t : ℂ) ^ (-s - 1))) t :=
    fun t ht ↦ (hasDerivAt_ofReal_cpow_const (hpos t ht).ne' hs0).const_sub _
  have hB : ∀ t ∈ Set.Icc a b, HasDerivAt (fun x : ℝ ↦ ‖s‖ / δ * (a ^ (-δ) - x ^ (-δ)))
      (‖s‖ / δ * -((-δ) * t ^ (-δ - 1))) t :=
    fun t ht ↦ ((Real.hasDerivAt_rpow_const (Or.inl (hpos t ht).ne')).const_sub _).const_mul _
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun x : ℝ ↦ (a : ℂ) ^ (-s) - (x : ℂ) ^ (-s)) (a := a) (b := b)
    (f' := fun t ↦ -(-s * (t : ℂ) ^ (-s - 1)))
    (B := fun x : ℝ ↦ ‖s‖ / δ * (a ^ (-δ) - x ^ (-δ)))
    (B' := fun t ↦ ‖s‖ / δ * -((-δ) * t ^ (-δ - 1)))
    (fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hf t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp)
    (fun t ht ↦ (hB t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hB t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    ?_ (Set.right_mem_Icc.mpr hab)
  intro t ht
  have ht1 : 1 ≤ t := ha.trans ht.1
  have htp : 0 < t := lt_of_lt_of_le one_pos ht1
  rw [norm_neg, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos htp]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  have h1 : t ^ (-s.re - 1) ≤ t ^ (-δ - 1) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have h2 : ‖s‖ / δ * -((-δ) * t ^ (-δ - 1)) = ‖s‖ * t ^ (-δ - 1) := by
    field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

theorem tendsto_rpow_neg {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    Tendsto (fun n : ℕ => ((n + N + 1 : ℕ) : ℝ) ^ (-δ)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ ((n + N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat (N + 1)).congr fun n ↦ by omega)
  exact (tendsto_rpow_neg_atTop hδ).comp h

theorem hasSum_telescope {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    HasSum (fun n : ℕ => ((n + N + 1 : ℕ) : ℝ) ^ (-δ) - ((n + N + 1 + 1 : ℕ) : ℝ) ^ (-δ))
      (((N + 1 : ℕ) : ℝ) ^ (-δ)) := by
  set g : ℕ → ℝ := fun n ↦ ((n + N + 1 : ℕ) : ℝ) ^ (-δ) with hg
  have hstep : ∀ n, ((n + N + 1 : ℕ) : ℝ) ^ (-δ) - ((n + N + 1 + 1 : ℕ) : ℝ) ^ (-δ) = g n - g (n + 1) := by
    intro n
    simp only [hg]
    rw [show n + 1 + N + 1 = n + N + 1 + 1 by omega]
  have hmono : ∀ n, 0 ≤ g n - g (n + 1) := by
    intro n
    refine sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith))
    exact_mod_cast (show n + N + 1 ≤ n + 1 + N + 1 by omega)
  simp_rw [hstep]
  rw [hasSum_iff_tendsto_nat_of_nonneg hmono]
  simp_rw [Finset.sum_range_sub']
  have h0 : g 0 = ((N + 1 : ℕ) : ℝ) ^ (-δ) := by
    simp only [hg, zero_add]
  rw [← h0]
  have h := (tendsto_const_nhds (x := g 0)).sub (tendsto_rpow_neg hδ N)
  rw [sub_zero] at h
  exact h

noncomputable def term {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) (s : ℂ) : ℂ :=
  (∑ k ∈ Finset.range (n + 1), χ ((k + 1 : ℕ) : ZMod q)) *
    (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 1 + 1 : ℕ) : ℂ) ^ (-s))

theorem abel {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s)
      = ∑ n ∈ Finset.range N, term χ n s
        + (∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ, ih, term]
    push_cast
    ring

theorem norm_term_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ)
    {δ R : ℝ} {s : ℂ} (hδ : 0 < δ) (hs : δ ≤ s.re) (hR : ‖s‖ ≤ R) :
    ‖term χ n s‖ ≤ q * (R / δ) *
      (((n + 1 : ℕ) : ℝ) ^ (-δ) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-δ)) := by
  have h1 := norm_sum_range_le χ hχ (n + 1)
  have h2 := norm_cpow_sub_le (a := ((n + 1 : ℕ) : ℝ)) (b := ((n + 1 + 1 : ℕ) : ℝ))
    (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast Nat.le_succ (n + 1)) hδ hs
  simp only [Complex.ofReal_natCast] at h2
  have hd : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-δ) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-δ) := by
    refine sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith))
    exact_mod_cast Nat.le_succ (n + 1)
  rw [term, norm_mul]
  calc _ ≤ (q : ℝ) * (‖s‖ / δ * (((n + 1 : ℕ) : ℝ) ^ (-δ) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-δ))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (q : ℝ) * (R / δ * (((n + 1 : ℕ) : ℝ) ^ (-δ) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-δ))) := by
        gcongr
    _ = _ := by ring

theorem summable_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : Summable (fun n => term χ n s) := by
  have hT : Summable (fun n : ℕ ↦ (q : ℝ) * (‖s‖ / s.re) *
      (((n + 1 : ℕ) : ℝ) ^ (-s.re) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-s.re))) :=
    ((hasSum_telescope hs 0).summable.mul_left ((q : ℝ) * (‖s‖ / s.re))).congr fun n ↦ by
      simp only [add_zero]
  exact Summable.of_norm_bounded hT fun n ↦ norm_term_le χ hχ n hs le_rfl le_rfl

theorem norm_boundary_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (N : ℕ) :
    ‖(∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s)‖
      ≤ q * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := by
  rw [norm_mul, norm_natCast_cpow_of_pos (Nat.succ_pos N), Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (norm_sum_range_le χ hχ N) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem LFunction_eq_tsum_of_one_lt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) : LFunction χ s = ∑' n, term χ n s := by
  have hs0 : 0 < s.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hL : HasSum (fun n : ℕ ↦ χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s))
      (LSeries (χ ·) s) := by
    have h := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs).hasSum
    rw [← hasSum_nat_add_iff' 1] at h
    simp only [Finset.range_one, Finset.sum_singleton, LSeries.term_zero, sub_zero] at h
    have e : (fun n : ℕ ↦ χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s)) =
        fun n ↦ LSeries.term (fun x ↦ χ x) s (n + 1) := by
      funext n
      rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
    rw [e]
    exact h
  have hB : Tendsto (fun N : ℕ ↦ (∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) *
      ((N + 1 : ℕ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N ↦ norm_boundary_le χ hχ s N) ?_
    simpa using (tendsto_rpow_neg hs0 0).const_mul (q : ℝ)
  have h3 := ((summable_term χ hχ hs0).hasSum.tendsto_sum_nat).add hB
  rw [add_zero] at h3
  exact tendsto_nhds_unique (hL.tendsto_sum_nat.congr fun N ↦ abel χ s N) h3

theorem LFunction_eq_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : LFunction χ s = ∑' n, term χ n s := by
  have hUo : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hc : ∀ m : ℕ, Differentiable ℂ (fun w : ℂ ↦ ((m + 1 : ℕ) : ℂ) ^ (-w)) := fun m w ↦
    differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast Nat.succ_ne_zero m))
  have hd : DifferentiableOn ℂ (fun z ↦ ∑' n, term χ n z) {z : ℂ | 0 < z.re} := by
    intro z hz
    have hz' : 0 < z.re := hz
    have hVo : IsOpen ({w : ℂ | z.re / 2 < w.re} ∩ Metric.ball 0 (‖z‖ + 1)) :=
      (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
    have hzV : z ∈ {w : ℂ | z.re / 2 < w.re} ∩ Metric.ball 0 (‖z‖ + 1) :=
      ⟨show z.re / 2 < z.re by linarith, by simp⟩
    have hsum : Summable (fun n : ℕ ↦ (q : ℝ) * ((‖z‖ + 1) / (z.re / 2)) *
        (((n + 1 : ℕ) : ℝ) ^ (-(z.re / 2)) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-(z.re / 2)))) :=
      ((hasSum_telescope (half_pos hz') 0).summable.mul_left
        ((q : ℝ) * ((‖z‖ + 1) / (z.re / 2)))).congr fun n ↦ by
        simp only [add_zero]
    have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun w ↦ term χ n w)
        ({w : ℂ | z.re / 2 < w.re} ∩ Metric.ball 0 (‖z‖ + 1)) := fun n ↦
      ((differentiable_const _).mul ((hc n).sub (hc (n + 1)))).differentiableOn
    have := differentiableOn_tsum_of_summable_norm hsum hdiff hVo fun n w hw ↦
      norm_term_le χ hχ n (half_pos hz') hw.1.le (mem_ball_zero_iff.mp hw.2).le
    exact ((this z hzV).differentiableAt (hVo.mem_nhds hzV)).differentiableWithinAt
  have hL := ((differentiable_LFunction hχ).differentiableOn (s := {z : ℂ | 0 < z.re})).analyticOnNhd hUo
  have hT := hd.analyticOnNhd hUo
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hev : LFunction χ =ᶠ[𝓝 (2 : ℂ)] fun z ↦ ∑' n, term χ n z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz
    exact LFunction_eq_tsum_of_one_lt χ hχ hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hT (convex_halfSpace_re_gt 0).isPreconnected h2 hev hs

theorem norm_LFunction_sub_sum_le :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 0 < s.re → ∀ N : ℕ, 1 ≤ N →
      ‖LFunction χ s - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖
        ≤ 2 * q * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
  intro q _ χ hχ s hs N hN
  have hsum : ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s) =
      ∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
    clear hN
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  have hsm := summable_term χ hχ hs
  have hsplit := hsm.sum_add_tsum_nat_add N
  rw [hsum, abel χ s N, LFunction_eq_tsum χ hχ hs, ← hsplit]
  set c : ℝ := (q : ℝ) * (‖s‖ / s.re)
  have htail : ‖∑' n, term χ (n + N) s‖ ≤ c * ((N + 1 : ℕ) : ℝ) ^ (-s.re) :=
    tsum_of_norm_bounded ((hasSum_telescope hs N).mul_left c) fun n ↦
      norm_term_le χ hχ (n + N) hs le_rfl le_rfl
  have hbd := norm_boundary_le χ hχ s N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : ((N + 1 : ℕ) : ℝ) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos hNpos (by push_cast; linarith) (by linarith)
  have hpow : 0 ≤ ((N + 1 : ℕ) : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hc0 : 0 ≤ c := by positivity
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hr : 0 ≤ ‖s‖ / s.re := by positivity
  calc ‖∑ i ∈ Finset.range N, term χ i s + ∑' n, term χ (n + N) s -
        (∑ i ∈ Finset.range N, term χ i s +
          (∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s))‖
      = ‖∑' n, term χ (n + N) s -
          (∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s)‖ := by
        congr 1
        ring
    _ ≤ ‖∑' n, term χ (n + N) s‖ +
          ‖(∑ k ∈ Finset.range N, χ ((k + 1 : ℕ) : ZMod q)) * ((N + 1 : ℕ) : ℂ) ^ (-s)‖ :=
        norm_sub_le _ _
    _ ≤ c * ((N + 1 : ℕ) : ℝ) ^ (-s.re) + q * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := add_le_add htail hbd
    _ = q * (1 + ‖s‖ / s.re) * ((N + 1 : ℕ) : ℝ) ^ (-s.re) := by ring
    _ ≤ q * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by gcongr
    _ ≤ 2 * q * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
        have : 0 ≤ (q : ℝ) * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by positivity
        nlinarith

end GlobalTheory.DirichletTail

import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

open Complex HurwitzZeta Filter Topology Set

namespace GroundTheory.Global.Quadratic

theorem hasDerivAt_add_cpow (n : ℕ) {t : ℝ} (ht : 0 < (n : ℝ) + t) (c : ℂ) :
    HasDerivAt (fun u : ℝ ↦ (((n : ℝ) + u : ℝ) : ℂ) ^ c)
      (c * (((n : ℝ) + t : ℝ) : ℂ) ^ (c - 1)) t := by
  have hs : ((n : ℂ) + (t : ℂ)) ∈ slitPlane := by
    have := Complex.ofReal_mem_slitPlane.2 ht
    push_cast at this
    exact this
  have h0 : HasDerivAt (fun w : ℂ ↦ ((n : ℂ) + w) ^ c) (c * ((n : ℂ) + (t : ℂ)) ^ (c - 1) * 1)
      (t : ℂ) :=
    ((hasDerivAt_id (t : ℂ)).const_add (n : ℂ)).cpow_const hs
  have h3 := h0.comp_ofReal
  push_cast
  simpa using h3

theorem norm_taylor_two_le (n : ℕ) (s : ℂ) {a b M : ℝ}
    (hpos : ∀ t ∈ uIcc a b, 0 < (n : ℝ) + t)
    (hM : ∀ t ∈ uIcc a b, ‖s * (s + 1) * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 2)‖ ≤ M) :
    ‖(((n : ℝ) + b : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + a : ℝ) : ℂ) ^ (-s) -
        (-s * (((n : ℝ) + a : ℝ) : ℂ) ^ (-s - 1)) * ((b - a : ℝ) : ℂ)‖ ≤ M * |b - a| ^ 2 := by
  have hconv : Convex ℝ (uIcc a b) := convex_uIcc a b
  have ha : a ∈ uIcc a b := left_mem_uIcc
  have hb : b ∈ uIcc a b := right_mem_uIcc

  set ψ : ℝ → ℂ := fun t ↦ -s * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 1) with hψ
  have hψd : ∀ t ∈ uIcc a b, HasDerivWithinAt ψ (s * (s + 1) * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 2))
      (uIcc a b) t := by
    intro t ht
    have h := (hasDerivAt_add_cpow n (hpos t ht) (-s - 1)).const_mul (-s)
    have he : -s * ((-s - 1) * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 1 - 1)) =
        s * (s + 1) * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 2) := by
      rw [show -s - 1 - 1 = -s - 2 by ring]
      ring
    rw [he] at h
    exact h.hasDerivWithinAt
  have hψb : ∀ t ∈ uIcc a b, ‖ψ t - ψ a‖ ≤ M * |b - a| := by
    intro t ht
    have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hψd hM ha ht
    refine h.trans (mul_le_mul_of_nonneg_left ?_ ((norm_nonneg _).trans (hM a ha)))
    rw [Real.norm_eq_abs]
    exact abs_sub_left_of_mem_uIcc ht

  set R : ℝ → ℂ := fun t ↦ (((n : ℝ) + t : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + a : ℝ) : ℂ) ^ (-s) -
    ψ a * ((t - a : ℝ) : ℂ) with hR
  have hRd : ∀ t ∈ uIcc a b, HasDerivWithinAt R (ψ t - ψ a) (uIcc a b) t := by
    intro t ht
    have h1 := hasDerivAt_add_cpow n (hpos t ht) (-s)
    have h2 : HasDerivAt (fun u : ℝ ↦ ψ a * ((u - a : ℝ) : ℂ)) (ψ a * 1) t := by
      have := ((hasDerivAt_id t).sub_const a).ofReal_comp.const_mul (ψ a)
      simpa using this
    have h3 := (h1.sub_const ((((n : ℝ) + a : ℝ) : ℂ) ^ (-s))).sub h2
    rw [mul_one] at h3
    have he : -s * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 1) = ψ t := rfl
    rw [he] at h3
    exact h3.hasDerivWithinAt
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hRd hψb ha hb
  have hRa : R a = 0 := by simp [hR]
  rw [hRa, sub_zero, Real.norm_eq_abs, mul_assoc, ← pow_two] at h
  exact h

theorem rpow_le_of_exponent_mem {b c e : ℝ} (hc : 0 < c) (hcb : c ≤ b) (he1 : -(9 / 2) ≤ e)
    (he2 : e ≤ -(3 / 2)) : b ^ e ≤ c ^ (-(3 / 2) : ℝ) + c ^ (-(9 / 2) : ℝ) := by
  have hb : 0 < b := hc.trans_le hcb
  have h1 : 0 ≤ c ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hc.le _
  have h2 : 0 ≤ c ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg hc.le _
  rcases le_or_gt 1 b with hb1 | hb1
  · calc b ^ e ≤ b ^ (-(3 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 he2
      _ ≤ c ^ (-(3 / 2) : ℝ) := Real.rpow_le_rpow_of_nonpos hc hcb (by norm_num)
      _ ≤ _ := le_add_of_nonneg_right h2
  · calc b ^ e ≤ b ^ (-(9 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_ge hb hb1.le he1
      _ ≤ c ^ (-(9 / 2) : ℝ) := Real.rpow_le_rpow_of_nonpos hc hcb (by norm_num)
      _ ≤ _ := le_add_of_nonneg_left h1

def hurwitzCombTerm (x : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (((n : ℝ) + x : ℝ) : ℂ) ^ (-s) + ((1 - 2 * x : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) +
    ((2 * x - 2 : ℝ) : ℂ) * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s)

def hurwitzComb (x : ℝ) (s : ℂ) : ℂ :=
  hurwitzZeta x s + ((1 - 2 * x : ℝ) : ℂ) * hurwitzZeta (1 : ℝ) s +
    ((2 * x - 2 : ℝ) : ℂ) * hurwitzZeta (1 / 2 : ℝ) s

theorem differentiable_hurwitzComb (x : ℝ) : Differentiable ℂ (hurwitzComb x) := by
  have hd : ∀ a b : UnitAddCircle, Differentiable ℂ (fun s ↦ hurwitzZeta a s - hurwitzZeta b s) := by
    intro a b
    have h := (differentiable_hurwitzZetaEven_sub_hurwitzZetaEven a b).add
      ((differentiable_hurwitzZetaOdd a).sub (differentiable_hurwitzZetaOdd b))
    have e : (fun s ↦ hurwitzZeta a s - hurwitzZeta b s) =
        (fun s ↦ hurwitzZetaEven a s - hurwitzZetaEven b s) + (hurwitzZetaOdd a - hurwitzZetaOdd b) := by
      funext s
      simp only [hurwitzZeta, Pi.add_apply, Pi.sub_apply]
      ring
    rw [e]
    exact h
  have h := (hd (x : UnitAddCircle) ((1 : ℝ) : UnitAddCircle)).add
    ((hd ((1 / 2 : ℝ) : UnitAddCircle) ((1 : ℝ) : UnitAddCircle)).const_mul ((2 * x - 2 : ℝ) : ℂ))
  have e : hurwitzComb x = (fun s ↦ hurwitzZeta (x : UnitAddCircle) s -
      hurwitzZeta ((1 : ℝ) : UnitAddCircle) s) + fun s ↦ ((2 * x - 2 : ℝ) : ℂ) *
        (hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) s - hurwitzZeta ((1 : ℝ) : UnitAddCircle) s) := by
    funext s
    simp only [hurwitzComb, Pi.add_apply]
    push_cast
    ring
  rw [e]
  exact h

theorem hasSum_hurwitzCombTerm {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ hurwitzCombTerm x n s) (hurwitzComb x s) := by
  have key : ∀ a : ℝ, a ∈ Icc (0 : ℝ) 1 →
      HasSum (fun n : ℕ ↦ (((n : ℝ) + a : ℝ) : ℂ) ^ (-s)) (hurwitzZeta a s) := by
    intro a ha
    refine (hasSum_hurwitzZeta_of_one_lt_re ha hs).congr_fun fun n ↦ ?_
    push_cast
    rw [cpow_neg, one_div]
  have h := ((key x ⟨hx0, hx1⟩).add ((key 1 ⟨zero_le_one, le_rfl⟩).mul_left ((1 - 2 * x : ℝ) : ℂ))).add
    ((key (1 / 2) ⟨by norm_num, by norm_num⟩).mul_left ((2 * x - 2 : ℝ) : ℂ))
  exact h

theorem norm_hurwitzCombTerm_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) {s : ℂ}
    (hs : s ∈ Metric.ball (1 : ℂ) (3 / 2)) :
    ‖hurwitzCombTerm x n s‖ ≤
      18 * (((n : ℝ) + min x (1 / 2)) ^ (-(3 / 2) : ℝ) + ((n : ℝ) + min x (1 / 2)) ^ (-(9 / 2) : ℝ)) := by
  set x₀ := min x (1 / 2) with hx₀
  have hx₀0 : 0 < x₀ := lt_min hx0 (by norm_num)
  set B := ((n : ℝ) + x₀) ^ (-(3 / 2) : ℝ) + ((n : ℝ) + x₀) ^ (-(9 / 2) : ℝ) with hB
  have hs1 : ‖s - 1‖ < 3 / 2 := by simpa [dist_eq_norm] using hs
  have hre : |s.re - 1| < 3 / 2 := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    linarith
  have hsn : ‖s‖ ≤ 5 / 2 := by
    have := norm_sub_norm_le s 1
    rw [norm_one] at this
    linarith
  have hsn1 : ‖s + 1‖ ≤ 7 / 2 := by
    have h1 : s + 1 = (s - 1) + 2 := by ring
    rw [h1]
    have := norm_add_le (s - 1) 2
    rw [Complex.norm_two] at this
    linarith

  have hM : ∀ t ∈ Icc x₀ 1, ‖s * (s + 1) * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 2)‖ ≤ 9 * B := by
    intro t ht
    have hpos' : 0 < (n : ℝ) + t := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (hx₀0.trans_le ht.1)
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos']
    have hre' : (-s - 2).re = -s.re - 2 := by simp
    rw [hre']
    have hb := rpow_le_of_exponent_mem (b := (n : ℝ) + t) (e := -s.re - 2)
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) hx₀0) (by linarith [ht.1])
      (by linarith [(abs_lt.1 hre).2]) (by linarith [(abs_lt.1 hre).1])
    have hB0 : 0 ≤ B := by positivity
    calc ‖s‖ * ‖s + 1‖ * ((n : ℝ) + t) ^ (-s.re - 2) ≤ (5 / 2) * (7 / 2) * B := by
          gcongr
      _ ≤ 9 * B := by nlinarith
  have hsub : ∀ c ∈ ({x, 1} : Set ℝ), uIcc (1 / 2) c ⊆ Icc x₀ 1 := by
    intro c hc
    refine uIcc_subset_Icc ⟨min_le_right _ _, by norm_num⟩ ?_
    rcases hc with rfl | rfl
    · exact ⟨min_le_left _ _, hx1.le⟩
    · exact ⟨by linarith [min_le_right x (1 / 2)], le_rfl⟩
  have hT : ∀ c ∈ ({x, 1} : Set ℝ), ‖(((n : ℝ) + c : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s) -
      (-s * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s - 1)) * ((c - 1 / 2 : ℝ) : ℂ)‖ ≤ 9 * B := by
    intro c hc
    have h := norm_taylor_two_le n s (a := 1 / 2) (b := c) (M := 9 * B)
      (fun t ht ↦ add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (hx₀0.trans_le (hsub c hc ht).1))
      (fun t ht ↦ hM t (hsub c hc ht))
    have hc' : |c - 1 / 2| ^ 2 ≤ 1 := by
      rcases hc with rfl | rfl
      · rw [sq_abs]
        nlinarith
      · norm_num
    have hB0 : 0 ≤ 9 * B := by positivity
    calc _ ≤ 9 * B * |c - 1 / 2| ^ 2 := h
      _ ≤ 9 * B * 1 := by gcongr
      _ = 9 * B := mul_one _
  have heq : hurwitzCombTerm x n s =
      ((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s) -
        (-s * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s - 1)) * ((x - 1 / 2 : ℝ) : ℂ)) +
      ((1 - 2 * x : ℝ) : ℂ) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s) -
        (-s * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s - 1)) * ((1 - 1 / 2 : ℝ) : ℂ)) := by
    simp only [hurwitzCombTerm]
    push_cast
    ring
  have hc2 : ‖((1 - 2 * x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  rw [heq]
  calc _ ≤ 9 * B + 1 * (9 * B) := by
        refine (norm_add_le _ _).trans (add_le_add (hT x (by simp)) ?_)
        rw [norm_mul]
        exact mul_le_mul hc2 (hT 1 (by simp)) (norm_nonneg _) zero_le_one
    _ = 18 * B := by ring

theorem summable_hurwitzCombBound {x₀ : ℝ} (hx₀ : 0 < x₀) :
    Summable (fun n : ℕ ↦ 18 * (((n : ℝ) + x₀) ^ (-(3 / 2) : ℝ) + ((n : ℝ) + x₀) ^ (-(9 / 2) : ℝ))) := by
  have key : ∀ p : ℝ, 1 < p → Summable (fun n : ℕ ↦ ((n : ℝ) + x₀) ^ (-p)) := by
    intro p hp
    refine ((Real.summable_one_div_nat_add_rpow x₀ p).2 hp).congr fun n ↦ ?_
    have h : 0 < (n : ℝ) + x₀ := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) hx₀
    rw [abs_of_pos h, Real.rpow_neg h.le, one_div]
  exact ((key _ (by norm_num)).add (key _ (by norm_num))).mul_left 18

theorem differentiableOn_tsum_hurwitzCombTerm {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    DifferentiableOn ℂ (fun s ↦ ∑' n, hurwitzCombTerm x n s) (Metric.ball 1 (3 / 2)) := by
  refine differentiableOn_tsum_of_summable_norm (summable_hurwitzCombBound (lt_min hx0 (by norm_num)))
    (fun n ↦ ?_) Metric.isOpen_ball (fun n s hs ↦ norm_hurwitzCombTerm_le hx0 hx1 n hs)
  have hd : ∀ a : ℝ, 0 < (n : ℝ) + a →
      Differentiable ℂ (fun s : ℂ ↦ (((n : ℝ) + a : ℝ) : ℂ) ^ (-s)) := fun a ha s ↦
    differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.2 ha.ne'))
  have hpos : ∀ a : ℝ, 0 < a → 0 < (n : ℝ) + a := fun a ha ↦
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha
  exact (((hd x (hpos x hx0)).add ((hd 1 (hpos 1 one_pos)).const_mul _)).add
    ((hd (1 / 2) (hpos _ (by norm_num))).const_mul _)).differentiableOn

theorem tsum_hurwitzCombTerm_eq {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {s : ℂ}
    (hs : s ∈ Metric.ball (1 : ℂ) (3 / 2)) :
    ∑' n, hurwitzCombTerm x n s = hurwitzComb x s := by
  have hU : IsOpen (Metric.ball (1 : ℂ) (3 / 2)) := Metric.isOpen_ball
  have hf : AnalyticOnNhd ℂ (fun s ↦ ∑' n, hurwitzCombTerm x n s) (Metric.ball 1 (3 / 2)) :=
    (differentiableOn_tsum_hurwitzCombTerm hx0 hx1).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (hurwitzComb x) (Metric.ball 1 (3 / 2)) :=
    (differentiable_hurwitzComb x).differentiableOn.analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ Metric.ball (1 : ℂ) (3 / 2) := by
    rw [Metric.mem_ball, dist_eq_norm, show (2 : ℂ) - 1 = 1 by norm_num, norm_one]
    norm_num
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_ball _ _).isPreconnected h2 ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  exact (hasSum_hurwitzCombTerm hx0.le hx1.le hz).tsum_eq

theorem hurwitzZeta_one_zero : hurwitzZeta ((1 : ℝ) : UnitAddCircle) 0 = -1 / 2 := by
  rw [show ((1 : ℝ) : UnitAddCircle) = 0 from AddCircle.coe_period 1, hurwitzZeta_zero,
    riemannZeta_zero]

theorem hurwitzZeta_half_zero : hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) 0 = 0 := by
  have hne : ((1 / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff 1).1 h
    rw [zsmul_eq_mul, mul_one] at hm
    have h1 : (0 : ℝ) < m := by rw [hm]; norm_num
    have h2 : (m : ℝ) < 1 := by rw [hm]; norm_num
    have h1' : 0 < m := by exact_mod_cast h1
    have h2' : m < 1 := by exact_mod_cast h2
    omega
  have hneg : -((1 / 2 : ℝ) : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_neg, show -(1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, AddCircle.coe_sub,
      AddCircle.coe_period 1, sub_zero]
  have hodd : hurwitzZetaOdd ((1 / 2 : ℝ) : UnitAddCircle) 0 = 0 := by
    have h := hurwitzZetaOdd_neg ((1 / 2 : ℝ) : UnitAddCircle) 0
    rw [hneg] at h
    have h2 : (2 : ℂ) * hurwitzZetaOdd ((1 / 2 : ℝ) : UnitAddCircle) 0 = 0 := by
      linear_combination h
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [hurwitzZeta, hurwitzZetaEven_apply_zero, if_neg hne, hodd, add_zero]

theorem hurwitzZeta_zero_eq {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - x := by
  have hterm : ∀ n : ℕ, hurwitzCombTerm x n 0 = 0 := fun n ↦ by
    simp only [hurwitzCombTerm, neg_zero, cpow_zero, mul_one]
    push_cast
    ring
  have h0 : hurwitzComb x 0 = 0 := by
    rw [← tsum_hurwitzCombTerm_eq hx0 hx1 (s := 0) (by
      rw [Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg, norm_one]; norm_num)]
    simp [hterm]
  simp only [hurwitzComb, hurwitzZeta_one_zero, hurwitzZeta_half_zero] at h0
  push_cast at h0
  linear_combination h0

theorem LFunction_zero_eq {N : ℕ} [NeZero N] {Φ : ZMod N → ℂ} (h0 : Φ 0 = 0)
    (hsum : ∑ j, Φ j = 0) :
    ZMod.LFunction Φ 0 = -(1 / N) * ∑ j : ZMod N, Φ j * (j.val : ℂ) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have key : ∀ j : ZMod N, Φ j * hurwitzZeta (ZMod.toAddCircle j) 0 =
      Φ j * (1 / 2 - (j.val : ℂ) / N) := by
    intro j
    by_cases hj : j = 0
    · rw [hj, h0, zero_mul, zero_mul]
    · have hv0 : 0 < j.val := Nat.pos_of_ne_zero fun h ↦ hj ((ZMod.val_eq_zero j).1 h)
      have hvN : j.val < N := ZMod.val_lt j
      rw [ZMod.toAddCircle_apply, hurwitzZeta_zero_eq (div_pos (Nat.cast_pos.2 hv0) hN)
        ((div_lt_one hN).2 (by exact_mod_cast hvN))]
      push_cast
      ring
  rw [ZMod.LFunction, neg_zero, cpow_zero, one_mul, Finset.sum_congr rfl fun j _ ↦ key j]
  have hs : ∑ j : ZMod N, Φ j * (1 / 2 - (j.val : ℂ) / N) =
      (∑ j, Φ j) * (1 / 2) - (1 / N) * ∑ j : ZMod N, Φ j * (j.val : ℂ) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hs, hsum]
  ring

theorem LFunction_zero_eq_of_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 0 = -(1 / N) * ∑ a : ZMod N, χ a * (a.val : ℂ) := by
  rcases eq_or_ne N 1 with rfl | hN1
  · exact absurd (MulChar.ext fun u ↦ by rw [Subsingleton.elim u 1, Units.val_one, map_one,
      map_one]) hχ
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 hN1
  exact LFunction_zero_eq (MulChar.map_nonunit χ not_isUnit_zero) (MulChar.sum_eq_zero_of_ne_one hχ)

end Quadratic

end GroundTheory.Global

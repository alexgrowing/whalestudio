import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfWeight

lemma one_add_abs_le_two_mul_exp_sq (x : ℝ) : 1 + |x| ≤ 2 * Real.exp (x ^ 2) := by
  have h1 : x ^ 2 + 1 ≤ Real.exp (x ^ 2) := Real.add_one_le_exp _
  have h2 : |x| ≤ 1 + x ^ 2 := by
    nlinarith [sq_abs x, sq_nonneg (|x| - 1), abs_nonneg x]
  nlinarith [sq_nonneg x]

lemma norm_half_add_le (s : ℂ) (a D L B : ℝ) (hL : L ≤ s.re) (hB : s.re ≤ B)
    (hD : |L| + |B| + |a| ≤ D) :
    ‖s / 2 + (a : ℂ)‖ ≤ 2 * (D + 1) * Real.exp (s.im ^ 2) := by
  have hre : |s.re| ≤ |L| + |B| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le L, abs_nonneg B]
    · linarith [le_abs_self B, abs_nonneg L]
  have hs : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  have h1 : ‖s / 2 + (a : ℂ)‖ ≤ ‖s‖ / 2 + |a| := by
    refine (norm_add_le _ _).trans ?_
    simp [Complex.norm_real]
  have hD0 : 0 ≤ D := by
    linarith [abs_nonneg L, abs_nonneg B, abs_nonneg a]
  have him := abs_nonneg s.im
  have h2 : ‖s / 2 + (a : ℂ)‖ ≤ (D + 1) * (1 + |s.im|) := by
    have h4 : 0 ≤ D * |s.im| := mul_nonneg hD0 him
    have h5 : (D + 1) * (1 + |s.im|) = D + 1 + D * |s.im| + |s.im| := by ring
    rw [h5]
    linarith [abs_nonneg L, abs_nonneg B, abs_nonneg a]
  have h3 := one_add_abs_le_two_mul_exp_sq s.im
  calc ‖s / 2 + (a : ℂ)‖ ≤ (D + 1) * (1 + |s.im|) := h2
    _ ≤ (D + 1) * (2 * Real.exp (s.im ^ 2)) := by
        exact mul_le_mul_of_nonneg_left h3 (by linarith)
    _ = 2 * (D + 1) * Real.exp (s.im ^ 2) := by ring

lemma mul_exp_le_of_abs_le {c E y : ℝ} (hy : 0 ≤ y) (hc : |c| ≤ E) :
    c * Real.exp (c * y) ≤ E * Real.exp (E * y) := by
  have hE : 0 ≤ E := (abs_nonneg c).trans hc
  have h1 : c ≤ E := (le_abs_self c).trans hc
  have h2 : Real.exp (c * y) ≤ Real.exp (E * y) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h1 hy)
  calc c * Real.exp (c * y) ≤ E * Real.exp (c * y) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ E * Real.exp (E * y) := mul_le_mul_of_nonneg_left h2 hE

lemma step_bound {n₁ n₂ p₁ p₂ c₁ c₂ D y x : ℝ} (m : ℕ) (hD : 0 ≤ D) (hy : 0 ≤ y) (hx : 0 < x)
    (hn₁0 : 0 ≤ n₁) (hn₂0 : 0 ≤ n₂) (hp₁0 : 0 ≤ p₁) (hp₂0 : 0 ≤ p₂)
    (hn₁ : n₁ ≤ 2 * (D + 1) * Real.exp y) (hn₂ : n₂ ≤ 2 * (D + 1) * Real.exp y)
    (hp₁ : p₁ ≤ c₁ * Real.exp (c₁ * y) / x ^ m) (hp₂ : p₂ ≤ c₂ * Real.exp (c₂ * y) / x ^ m) :
    (n₁ * p₁ + n₂ * p₂) / (2 * Real.pi * x) ≤
      (4 * (D + 1) * (|c₁| + |c₂|) + (|c₁| + |c₂|) + 1) *
        Real.exp ((4 * (D + 1) * (|c₁| + |c₂|) + (|c₁| + |c₂|) + 1) * y) / x ^ (m + 1) := by
  set E := |c₁| + |c₂| with hEdef
  have hE : 0 ≤ E := by positivity
  have ht : 0 < x ^ m := pow_pos hx m
  have hexpE := Real.exp_pos (E * y)
  have hexpy := Real.exp_pos y
  set Q := E * Real.exp (E * y) / x ^ m with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hq₁ : p₁ ≤ Q := hp₁.trans (div_le_div_of_nonneg_right
    (mul_exp_le_of_abs_le hy (by rw [hEdef]; linarith [abs_nonneg c₂])) ht.le)
  have hq₂ : p₂ ≤ Q := hp₂.trans (div_le_div_of_nonneg_right
    (mul_exp_le_of_abs_le hy (by rw [hEdef]; linarith [abs_nonneg c₁])) ht.le)
  set P := 2 * (D + 1) * Real.exp y with hP
  have hP0 : 0 ≤ P := by positivity
  have hsum : n₁ * p₁ + n₂ * p₂ ≤ 2 * (P * Q) := by
    have := mul_le_mul hn₁ hq₁ hp₁0 hP0
    have := mul_le_mul hn₂ hq₂ hp₂0 hP0
    linarith
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hden : x ≤ 2 * Real.pi * x := by nlinarith
  have h1 : (n₁ * p₁ + n₂ * p₂) / (2 * Real.pi * x) ≤ 2 * (P * Q) / x := by
    calc (n₁ * p₁ + n₂ * p₂) / (2 * Real.pi * x) ≤ (n₁ * p₁ + n₂ * p₂) / x :=
          div_le_div_of_nonneg_left (by positivity) hx hden
      _ ≤ 2 * (P * Q) / x := div_le_div_of_nonneg_right hsum hx.le
  have h2 : 2 * (P * Q) / x =
      (4 * (D + 1) * E * Real.exp ((E + 1) * y)) / x ^ (m + 1) := by
    have hsplit : Real.exp ((E + 1) * y) = Real.exp (E * y) * Real.exp y := by
      rw [← Real.exp_add]
      ring_nf
    rw [hP, hQ, pow_succ, hsplit]
    field_simp
    <;> ring
  rw [h2] at h1
  refine h1.trans (div_le_div_of_nonneg_right ?_ (pow_pos hx _).le)
  set C := 4 * (D + 1) * E + E + 1 with hC
  have hc1 : 4 * (D + 1) * E ≤ C := by rw [hC]; linarith
  have hc2 : E + 1 ≤ C := by
    have : 0 ≤ 4 * (D + 1) * E := by positivity
    rw [hC]; linarith
  have hexp : Real.exp ((E + 1) * y) ≤ Real.exp (C * y) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc2 hy)
  exact mul_le_mul hc1 hexp (Real.exp_pos _).le (by linarith)

theorem kernel_fourier_continuation_decay : W0 → W1 → W2 := by
  intro h0 h1 m
  induction m with
  | zero =>
    intro a b
    refine ⟨fun s ξ => Phi (s / 2 + a) (s / 2 + b) ξ, ?_, ?_, ?_, ?_⟩
    · intro ξ
      simpa using (h0 a b).1 ξ
    · intro s hs
      have hs' : s ∈ HP (1 - a - b) := by simpa using hs
      exact ((h0 a b).2.1 s hs').2.measurable
    · intro s _ ξ _
      rfl
    · intro δ B hδ
      obtain ⟨C, hC⟩ := (h0 a b).2.2 δ B hδ
      refine ⟨C, fun s ξ _ hl hu => ?_⟩
      simpa using hC s ξ (by simpa using hl) hu
  | succ m ih =>
    intro a b
    obtain ⟨P₁, d₁, m₁, e₁, b₁⟩ := ih (a + 1) b
    obtain ⟨P₂, d₂, m₂, e₂, b₂⟩ := ih a (b + 1)
    have hr₁ : 1 - (a + 1) - b - (m : ℝ) = 1 - a - b - ((m + 1 : ℕ) : ℝ) := by
      push_cast; ring
    have hr₂ : 1 - a - (b + 1) - (m : ℝ) = 1 - a - b - ((m + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [hr₁] at d₁ m₁
    rw [hr₂] at d₂ m₂
    refine ⟨fun s ξ => ((s / 2 + a) * P₁ s ξ - (s / 2 + b) * P₂ s ξ) / (2 * (Real.pi : ℂ) * ξ),
      ?_, ?_, ?_, ?_⟩
    · intro ξ
      have hlin : ∀ c : ℝ, DifferentiableOn ℂ (fun s : ℂ => s / 2 + (c : ℂ))
          (HP (1 - a - b - ((m + 1 : ℕ) : ℝ))) := fun c =>
        ((differentiable_id.div_const 2).add_const _).differentiableOn
      exact (((hlin a).mul (d₁ ξ)).sub ((hlin b).mul (d₂ ξ))).div_const _
    · intro s hs
      have hcast : Measurable fun ξ : ℝ => (2 * (Real.pi : ℂ) * (ξ : ℂ)) :=
        measurable_const.mul Complex.measurable_ofReal
      exact (((m₁ s hs).const_mul _).sub ((m₂ s hs).const_mul _)).div hcast
    · intro s hs ξ hξ
      have hs₁ : s ∈ HP (1 - (a + 1) - b) := by
        have : 1 - a - b < s.re := hs
        show 1 - (a + 1) - b < s.re
        linarith
      have hs₂ : s ∈ HP (1 - a - (b + 1)) := by
        have : 1 - a - b < s.re := hs
        show 1 - a - (b + 1) < s.re
        linarith
      have hre : 1 < (s / 2 + (a : ℂ) + (s / 2 + (b : ℂ))).re := by
        have : 1 - a - b < s.re := hs
        simp
        linarith
      have hW := (h1 _ _ hre).1 ξ
      have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have ha : s / 2 + ((a + 1 : ℝ) : ℂ) = s / 2 + (a : ℂ) + 1 := by push_cast; ring
      have hb : s / 2 + ((b + 1 : ℝ) : ℂ) = s / 2 + (b : ℂ) + 1 := by push_cast; ring
      show ((s / 2 + a) * P₁ s ξ - (s / 2 + b) * P₂ s ξ) / (2 * (Real.pi : ℂ) * ξ) = _
      rw [e₁ s hs₁ ξ hξ, e₂ s hs₂ ξ hξ, ha, hb, ← hW]
      field_simp
    · intro δ B hδ
      obtain ⟨c₁, hc₁⟩ := b₁ δ B hδ
      obtain ⟨c₂, hc₂⟩ := b₂ δ B hδ
      set L := 1 - a - b - ((m + 1 : ℕ) : ℝ) + δ with hL
      set D := |L| + |B| + |a| + |b| with hDdef
      have hD : 0 ≤ D := by positivity
      refine ⟨4 * (D + 1) * (|c₁| + |c₂|) + (|c₁| + |c₂|) + 1, fun s ξ hξ hl hu => ?_⟩
      have hx : 0 < |ξ| := abs_pos.mpr hξ
      have hl₁ : 1 - (a + 1) - b - (m : ℝ) + δ ≤ s.re := by rw [hr₁]; exact hl
      have hl₂ : 1 - a - (b + 1) - (m : ℝ) + δ ≤ s.re := by rw [hr₂]; exact hl
      have hna := norm_half_add_le s a D L B hl hu
        (by rw [hDdef]; linarith [abs_nonneg b])
      have hnb := norm_half_add_le s b D L B hl hu
        (by rw [hDdef]; linarith [abs_nonneg a])
      have key := step_bound (x := |ξ|) (y := s.im ^ 2) m hD (sq_nonneg _) hx
        (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hna hnb
        (hc₁ s ξ hξ hl₁ hu) (hc₂ s ξ hξ hl₂ hu)
      refine le_trans ?_ key
      have hden : ‖2 * (Real.pi : ℂ) * (ξ : ℂ)‖ = 2 * Real.pi * |ξ| := by
        simp [Complex.norm_real, abs_of_pos Real.pi_pos]
      show ‖((s / 2 + a) * P₁ s ξ - (s / 2 + b) * P₂ s ξ) / (2 * (Real.pi : ℂ) * ξ)‖ ≤ _
      rw [norm_div, hden]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]

end GlobalTheory.CompanionTheory.HalfWeight

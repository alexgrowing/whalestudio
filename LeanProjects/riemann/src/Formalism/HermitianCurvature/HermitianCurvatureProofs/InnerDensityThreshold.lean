import Formalism.HermitianCurvature.BigCellVanishingOfCommute

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

set_option maxHeartbeats 2000000 in
theorem inner_density_threshold : C6.DensThreshJ := by
  intro C₁ c₃ C₂ hC₁ hc₃
  set K : ℝ := 24 * C₁ + 192 * c₃ + 5 * (C₂ : ℝ) + 80 with hK
  refine ⟨⌈K⌉₊, ?_⟩
  intro CV hCV r n s A hr hn hs hA
  have hKV : K ≤ (CV : ℝ) := le_trans (Nat.le_ceil K) (by exact_mod_cast hCV)
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have hsx : (s:ℝ) ≤ r := by exact_mod_cast hs
  have hy : (1:ℝ) ≤ n := by linarith
  have hK0 : 0 ≤ K := by positivity
  have hA' : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) ≤ A := by
    unfold C6.AV at hA
    have e : (r:ℝ) * ((CV:ℝ) * ((r:ℝ) ^ 3 * n + (n:ℝ) ^ 2 + (r:ℝ) ^ 4)) =
        (CV:ℝ) * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) + (CV:ℝ) * ((r:ℝ) * n ^ 2) := by ring
    rw [e] at hA
    have : 0 ≤ (CV:ℝ) * ((r:ℝ) * n ^ 2) := by positivity
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) ≤ (CV:ℝ) * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) :=
      mul_le_mul_of_nonneg_right hKV (by positivity)
    linarith
  have hs2 : (s:ℝ) ^ 2 ≤ (r:ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hsx 2
  have h8 : 8 * (2 * (r:ℝ) + 1) ≤ 24 * r := by linarith
  have x35 : (r:ℝ) ^ 3 ≤ (r:ℝ) ^ 5 := pow_le_pow_right₀ hx (by norm_num)
  have x15 : (r:ℝ) ≤ (r:ℝ) ^ 5 := by
    calc (r:ℝ) = (r:ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hx (by norm_num)
  have x24 : (r:ℝ) ^ 2 * n ≤ (r:ℝ) ^ 4 * n :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hx (by norm_num)) (by positivity)
  have hpos : (0:ℝ) < 8 * (2 * (r:ℝ) + 1) := by positivity

  have hb : 5 * (r:ℝ) * (((C₂ * s ^ 2 : ℕ) : ℝ) + 1) + 2 * (r:ℝ) * ((1 : ℕ) : ℝ) ≤
      (5 * (C₂:ℝ) + 7) * (r:ℝ) ^ 5 := by
    push_cast
    have : (C₂:ℝ) * (s:ℝ) ^ 2 ≤ (C₂:ℝ) * (r:ℝ) ^ 2 := mul_le_mul_of_nonneg_left hs2 (by positivity)
    have e : 5 * (r:ℝ) * ((C₂:ℝ) * (r:ℝ) ^ 2 + 1) + 2 * (r:ℝ) = 5 * (C₂:ℝ) * (r:ℝ) ^ 3 + 7 * r := by ring
    have h3 : 5 * (r:ℝ) * ((C₂:ℝ) * (s:ℝ) ^ 2 + 1) ≤ 5 * (r:ℝ) * ((C₂:ℝ) * (r:ℝ) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have := mul_le_mul_of_nonneg_left x35 (by positivity : (0:ℝ) ≤ 5 * (C₂:ℝ))
    nlinarith
  have key : ∀ X : ℝ, X * (8 * (2 * (r:ℝ) + 1)) + (5 * C₂ + 7) * (r:ℝ) ^ 5 ≤ A → X ≤ U.a1 r A (C₂ * s ^ 2) 1 := by
    intro X hX
    unfold U.a1
    rw [le_div_iff₀ hpos]
    linarith
  have hx5 : 0 ≤ (r:ℝ) ^ 5 := by positivity
  have hx4y : 0 ≤ (r:ℝ) ^ 4 * n := by positivity
  refine ⟨key _ ?_, key _ ?_, key _ ?_⟩
  · have a : C₁ * (s:ℝ) ^ 2 * (8 * (2 * (r:ℝ) + 1)) ≤ C₁ * (r:ℝ) ^ 2 * (24 * r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs2 hC₁) h8 (by positivity) (by positivity)
    have e : C₁ * (r:ℝ) ^ 2 * (24 * r) = 24 * C₁ * (r:ℝ) ^ 3 := by ring
    have := mul_le_mul_of_nonneg_left x35 (by positivity : (0:ℝ) ≤ 24 * C₁)
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) = K * ((r:ℝ) ^ 4 * n) + K * (r:ℝ) ^ 5 := by ring
    have : 0 ≤ K * ((r:ℝ) ^ 4 * n) := by positivity
    have : 0 ≤ 192 * c₃ * (r:ℝ) ^ 5 := by positivity
    have : K * (r:ℝ) ^ 5 = (24 * C₁ + 5 * C₂ + 7) * (r:ℝ) ^ 5 + 192 * c₃ * (r:ℝ) ^ 5 + 73 * (r:ℝ) ^ 5 := by
      rw [hK]; ring
    nlinarith
  · have q1 : ((r:ℝ) + 1) ^ 2 ≤ 4 * (r:ℝ) ^ 2 := by nlinarith
    have q2 : (r:ℝ) * n + 1 ≤ 2 * ((r:ℝ) * n) := by nlinarith
    have q : ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1)) ≤
        4 * (r:ℝ) ^ 2 * (2 * ((r:ℝ) * n)) * (24 * r) :=
      mul_le_mul (mul_le_mul q1 q2 (by positivity) (by positivity)) h8 (by positivity) (by positivity)
    have e : 4 * (r:ℝ) ^ 2 * (2 * ((r:ℝ) * n)) * (24 * r) = 192 * ((r:ℝ) ^ 4 * n) := by ring
    have := mul_le_mul_of_nonneg_left q hc₃
    have : c₃ * ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1)) =
        c₃ * (((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1))) := by ring
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) = (192 * c₃) * ((r:ℝ) ^ 4 * n) + (5 * C₂ + 7) * (r:ℝ) ^ 5 +
        ((24 * C₁ + 5 * C₂ + 80) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5) := by rw [hK]; ring
    have : 0 ≤ (24 * C₁ + 5 * C₂ + 80) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5 := by positivity
    nlinarith
  · have q : (2 * (r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1)) ≤ (3 * ((r:ℝ) * n)) * (24 * r) :=
      mul_le_mul (by nlinarith) h8 (by positivity) (by positivity)
    have e : (3 * ((r:ℝ) * n)) * (24 * r) = 72 * ((r:ℝ) ^ 2 * n) := by ring
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) = 72 * ((r:ℝ) ^ 4 * n) + (5 * C₂ + 7) * (r:ℝ) ^ 5 +
        ((24 * C₁ + 192 * c₃ + 5 * C₂ + 8) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5) := by rw [hK]; ring
    have : 0 ≤ (24 * C₁ + 192 * c₃ + 5 * C₂ + 8) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5 := by positivity
    nlinarith

set_option maxHeartbeats 2000000 in
theorem top_density_threshold : C6.DensThreshTop := by
  intro C₁ C C₂ hC₁ hC
  set K : ℝ := 40 * C₁ + 80 + 12 * C + 4 * C * C₂ + 2 * (C₂ : ℝ) + 1 with hK
  refine ⟨⌈K⌉₊, ?_⟩
  intro CV hCV r n s al A hr hn hs hal hA
  have hKV : K ≤ (CV : ℝ) := le_trans (Nat.le_ceil K) (by exact_mod_cast hCV)
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have hsx : (s:ℝ) ≤ r + 1 := by exact_mod_cast hs
  have hal' : (al:ℝ) ≤ C₂ * (s:ℝ) ^ 2 := by exact_mod_cast hal
  have hy : (1:ℝ) ≤ n := by linarith
  have hK0 : 0 ≤ K := by positivity
  constructor
  · have hA' : K * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) ≤ A := by
      unfold C6.AV at hA
      have e : (r:ℝ) * ((CV:ℝ) * ((r:ℝ) ^ 3 * n + (n:ℝ) ^ 2 + (r:ℝ) ^ 4)) =
          (CV:ℝ) * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) + (CV:ℝ) * ((r:ℝ) ^ 4 * n) := by ring
      rw [e] at hA
      have : 0 ≤ (CV:ℝ) * ((r:ℝ) ^ 4 * n) := by positivity
      have : K * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) ≤ (CV:ℝ) * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) :=
        mul_le_mul_of_nonneg_right hKV (by positivity)
      linarith
    have hs2 : (s:ℝ) ^ 2 ≤ 4 * (r:ℝ) ^ 2 := by
      have : (s:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hsx 2
      nlinarith
    have hR2 : ((r:ℝ) + 1) ^ 2 ≤ 4 * (r:ℝ) ^ 2 := by nlinarith
    have x35 : (r:ℝ) ^ 3 ≤ (r:ℝ) ^ 5 := pow_le_pow_right₀ hx (by norm_num)
    have hpos : (0:ℝ) < 5 * ((r:ℝ) + 1) := by positivity
    rw [le_sub_iff_add_le, le_div_iff₀ hpos, le_sub_iff_add_le]

    have b1 : (C₁ * (s:ℝ) ^ 2 + 2 * ((r:ℝ) + 1) ^ 2 + C * (r:ℝ) ^ 2) ≤ (4 * C₁ + 8 + C) * (r:ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hs2 hC₁
      nlinarith
    have b2 : (C₁ * (s:ℝ) ^ 2 + 2 * ((r:ℝ) + 1) ^ 2 + C * (r:ℝ) ^ 2) * (5 * ((r:ℝ) + 1)) ≤
        (4 * C₁ + 8 + C) * (r:ℝ) ^ 2 * (10 * r) :=
      mul_le_mul b1 (by linarith) (by positivity) (by positivity)
    have b3 : (r:ℝ) * al ≤ 4 * C₂ * (r:ℝ) ^ 3 := by
      have : (al:ℝ) ≤ C₂ * (4 * (r:ℝ) ^ 2) := le_trans hal' (mul_le_mul_of_nonneg_left hs2 (by positivity))
      have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ r)
      nlinarith
    have b4 : (n:ℝ) ^ 2 ≤ (r:ℝ) * n ^ 2 := by nlinarith [sq_nonneg (n:ℝ)]
    have b5 : C * ((n:ℝ) ^ 2 + (r:ℝ) ^ 3 + r * al) ≤ C * ((r:ℝ) * n ^ 2) + (C + 4 * C * C₂) * (r:ℝ) ^ 5 := by
      have : (n:ℝ) ^ 2 + (r:ℝ) ^ 3 + r * al ≤ (r:ℝ) * n ^ 2 + (1 + 4 * C₂) * (r:ℝ) ^ 5 := by nlinarith
      have := mul_le_mul_of_nonneg_left this hC
      nlinarith
    have e : (4 * C₁ + 8 + C) * (r:ℝ) ^ 2 * (10 * r) = (40 * C₁ + 80 + 10 * C) * (r:ℝ) ^ 3 := by ring
    have b6 := mul_le_mul_of_nonneg_left x35 (by positivity : (0:ℝ) ≤ 40 * C₁ + 80 + 10 * C)
    have : K * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) = C * ((r:ℝ) * n ^ 2) + (C + 4 * C * C₂) * (r:ℝ) ^ 5 +
        (40 * C₁ + 80 + 10 * C) * (r:ℝ) ^ 5 +
        ((40 * C₁ + 80 + 11 * C + 4 * C * C₂ + 2 * C₂ + 1) * ((r:ℝ) * n ^ 2) + (C + 2 * C₂ + 1) * (r:ℝ) ^ 5) := by
      rw [hK]; ring
    have : 0 ≤ (40 * C₁ + 80 + 11 * C + 4 * C * C₂ + 2 * C₂ + 1) * ((r:ℝ) * n ^ 2) + (C + 2 * C₂ + 1) * (r:ℝ) ^ 5 := by
      positivity
    nlinarith
  · have hK2 : (2 * C₂ + 1 : ℝ) ≤ K := by
      rw [hK]; have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC) (Nat.cast_nonneg (α := ℝ) C₂); linarith
    have h2 : (2 * C₂ + 1 : ℝ) ≤ CV := le_trans hK2 hKV
    unfold C6.mmV
    have hR : ((C₂ * s ^ 2 + 1 : ℕ) : ℝ) ≤ ((CV * (r ^ 2 + 1) : ℕ) : ℝ) := by
      push_cast
      have q1 : (s:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hsx 2
      have q2 : ((r:ℝ) + 1) ^ 2 ≤ 2 * ((r:ℝ) ^ 2 + 1) := by nlinarith [sq_nonneg ((r:ℝ) - 1)]
      have q3 : (C₂:ℝ) * (s:ℝ) ^ 2 ≤ (C₂:ℝ) * (2 * ((r:ℝ) ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left (le_trans q1 q2) (by positivity)
      have q4 : (2 * (C₂:ℝ) + 1) * ((r:ℝ) ^ 2 + 1) ≤ (CV:ℝ) * ((r:ℝ) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have q5 : (1:ℝ) ≤ (r:ℝ) ^ 2 + 1 := by nlinarith
      nlinarith
    exact_mod_cast hR

end Formalism.FourierDecayAlt.P

import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

open Formalism.BasicNotions GlobalTheory.EX

theorem UpperTheory.Top.eventually_rank_le_rpow_of_lt_one_div_fiftytwo :
    ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      (R.t : ℝ) ≤ s.x ^ (400 : ℝ) := by
  intro eps he0 he1
  refine ⟨(2:ℝ) ^ 100, ?_⟩
  intro s R hs hx hR
  have hX1 : 1 < s.x := s.one_lt_alt
  have hX0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have he' := s.eps_lt
  have hnle := hR.n_le
  obtain ⟨⟨-, -⟩, ⟨hm1, -⟩, ⟨-, hk2⟩, heq⟩ := hR
  have hmono : ∀ a b : ℝ, a ≤ b → s.x ^ a ≤ s.x ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le hX1.le h
  have hY : ∀ n : ℕ, s.x ^ ((n:ℝ) / 100) = (s.x ^ ((1:ℝ) / 100)) ^ n := by
    intro n
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    ring_nf
  have hY100 : (s.x ^ ((1:ℝ) / 100)) ^ 100 = s.x := by
    rw [← hY 100]; norm_num
  have hY2 : (2:ℝ) ≤ s.x ^ ((1:ℝ) / 100) := by
    have h := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 2 ^ 100) hx (by norm_num : (0:ℝ) ≤ 1 / 100)
    have h2 : ((2:ℝ) ^ 100) ^ ((1:ℝ) / 100) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  generalize hYd : s.x ^ ((1:ℝ) / 100) = Y at hY hY100 hY2
  have hY1 : (1:ℝ) ≤ Y := by linarith
  have hY0 : (0:ℝ) < Y := by linarith
  have hn : (R.n : ℝ) ≤ 2 * Y ^ 216 := by
    have h := hmono _ _ (show 2 + 8 * s.eps + s.eps / 100 ≤ ((216:ℕ):ℝ) / 100 by push_cast; linarith)
    rw [hY] at h
    linarith
  have hfe : (R.f : ℝ) = 2 * (R.n : ℝ) := by
    simp only [Ranks.f, Nat.cast_mul, Nat.cast_ofNat]
  have hf : (R.f : ℝ) ≤ 4 * Y ^ 216 := by linarith
  have hk : (R.k : ℝ) ≤ 2 * Y ^ 470 := by
    have h := hmono _ _ (show 9 / 2 + 10 * s.eps ≤ ((470:ℕ):ℝ) / 100 by push_cast; linarith)
    rw [hY] at h
    linarith
  have hm : Y ^ 49 ≤ (R.m : ℝ) := by
    refine le_trans ?_ hm1
    rw [Real.le_sqrt (by positivity) (by unfold Scale.delta1; positivity)]
    have h1 : (Y ^ 49) ^ 2 = s.x ^ (((98:ℕ):ℝ) / 100) := by rw [hY]; ring
    have h2 : s.x * s.delta1 = s.x ^ ((1:ℝ) + -(s.eps / 8)) := by
      rw [Real.rpow_add hX0, Real.rpow_one]; rfl
    rw [h1, h2]
    exact hmono _ _ (by push_cast; linarith)
  have hm0 : (0:ℝ) < R.m := lt_of_lt_of_le (by positivity) hm
  have hL : s.L ^ 2 ≤ Y ^ 4 := by
    have h1 : s.L ^ 2 = s.x ^ (s.eps * 2) := by
      rw [Real.rpow_mul hX0.le, Real.rpow_two]; rfl
    rw [h1]
    have h := hmono _ _ (show s.eps * 2 ≤ ((4:ℕ):ℝ) / 100 by push_cast; linarith)
    rw [hY] at h
    exact h
  have hr : (R.r : ℝ) ≤ 4 * Y ^ 470 := by
    have h : R.r ≤ 2 * R.k := by
      have := R.m_add_three_le_k
      unfold Ranks.r
      omega
    have h' : (R.r : ℝ) ≤ 2 * (R.k : ℝ) := by exact_mod_cast h
    linarith
  have hk5 : (5:ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    have := R.two_le_m
    exact_mod_cast (by omega : 5 ≤ R.k)
  have hk0 : (0:ℝ) ≤ (R.k : ℝ) - 1 := by linarith
  have hk' : (R.k : ℝ) - 1 ≤ 2 * Y ^ 470 := by linarith
  have hf0 : (0:ℝ) ≤ R.f := by positivity
  have hBq : 0 ≤ (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hk0 3)) (by positivity)) hm0.le
  have hB : (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m ≤ 128 * Y ^ 1797 := by
    rw [div_le_iff₀ hm0]
    calc (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2
        ≤ (4 * Y ^ 216) ^ 2 * (2 * Y ^ 470) ^ 3 * Y ^ 4 := by gcongr
      _ = 128 * Y ^ 1797 * Y ^ 49 := by ring
      _ ≤ 128 * Y ^ 1797 * R.m := by gcongr
  have hp1 : Y ^ 216 ≤ Y ^ 1797 := pow_le_pow_right₀ hY1 (by norm_num)
  have hQ : (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m ≤ 132 * Y ^ 1797 := by
    linarith
  have hQ0 : 0 ≤ (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by linarith
  have hr0 : (0:ℝ) ≤ R.r := by positivity
  have hW : (nWv R s : ℝ) ≤ 5288 * Y ^ 2267 := by
    have hy0 : (0:ℝ) ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 :=
      div_nonneg (mul_nonneg (by positivity) hQ0) (by norm_num)
    have hc := Nat.ceil_lt_add_one hy0
    have hyb : 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m)
        ≤ 10 * (4 * Y ^ 470) * (132 * Y ^ 1797) :=
      mul_le_mul (by linarith) hQ hQ0 (by positivity)
    have hY2267 : (1:ℝ) ≤ Y ^ 2267 := one_le_pow₀ hY1
    have e1 : 10 * (4 * Y ^ 470) * (132 * Y ^ 1797) = 5280 * Y ^ 2267 := by ring
    unfold nWv
    push_cast
    linarith
  have hT : (TOv s : ℝ) ≤ 2 * Y ^ 37700 := by
    have hc := Nat.ceil_lt_add_one (show (0:ℝ) ≤ s.x ^ (377:ℝ) by positivity)
    have h1 : s.x ^ (377:ℝ) = Y ^ 37700 := by
      rw [show (377:ℝ) = ((37700:ℕ):ℝ) / 100 by norm_num, hY]
    have h2 : (1:ℝ) ≤ Y ^ 37700 := one_le_pow₀ hY1
    unfold TOv
    linarith
  have heqR : (R.r : ℝ) + R.t = 8 * R.f * R.r + 4 + (TOv s : ℝ) * (nWv R s : ℝ) := by
    exact_mod_cast heq
  have hfr : (R.f : ℝ) * R.r ≤ (4 * Y ^ 216) * (4 * Y ^ 470) :=
    mul_le_mul hf hr hr0 (by positivity)
  have hTW : (TOv s : ℝ) * nWv R s ≤ (2 * Y ^ 37700) * (5288 * Y ^ 2267) :=
    mul_le_mul hT hW (by positivity) (by positivity)
  rw [show (400:ℝ) = ((40000:ℕ):ℝ) / 100 by norm_num, hY]
  have e1 : (4 * Y ^ 216) * (4 * Y ^ 470) = 16 * Y ^ 686 := by ring
  have e2 : (2 * Y ^ 37700) * (5288 * Y ^ 2267) = 10576 * Y ^ 39967 := by ring
  have p1 : Y ^ 686 ≤ Y ^ 39967 := pow_le_pow_right₀ hY1 (by norm_num)
  have p2 : (1:ℝ) ≤ Y ^ 39967 := one_le_pow₀ hY1
  have p3 : (10708:ℝ) ≤ Y ^ 33 := by
    have := pow_le_pow_left₀ (by norm_num) hY2 33
    norm_num at this
    linarith
  have e3 : Y ^ 40000 = Y ^ 33 * Y ^ 39967 := by ring
  have p4 : (10708:ℝ) * Y ^ 39967 ≤ Y ^ 33 * Y ^ 39967 :=
    mul_le_mul_of_nonneg_right p3 (by positivity)
  rw [e3]
  linarith

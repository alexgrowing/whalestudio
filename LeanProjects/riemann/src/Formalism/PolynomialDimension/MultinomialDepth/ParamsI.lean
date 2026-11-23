import Mathlib
import Formalism.PolynomialDimension.StatementNum

noncomputable section

namespace Formalism.CountingSumsFrames

open Real

namespace ParamsIProof

theorem one_le_log_of_three_le (a : ℝ) (ha : 3 ≤ a) : 1 ≤ Real.log a := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

theorem margin (C Cm N1 k Q c La b' Ib X Nr Y : ℝ)
    (hCm : 1 ≤ Cm) (hC : 1000 * Cm ≤ C) (hN1 : 1 ≤ N1) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hLa : 1 ≤ La) (hIb : 0 ≤ Ib) (hb : 0 < b') (hc0 : 0 ≤ c) (hc : c ≤ 4 * X) (hX : 0 ≤ X)
    (hN : 1 ≤ Nr) (hY : 1 ≤ Y) (hb' : C * k ^ 3 * Nr * Q ^ 4 * X * Y ≤ b') :
    ∀ Ai : ℝ, b' / (2 * Q) ≤ Ai →
      2 * (Cm * k * N1 * Q * c) + 12 * c ≤ (C * N1 * La / k + 2 * Ib / b') * Ai / 4 := by
  intro Ai hAi
  have hQ0 : 0 < Q := by linarith
  have hk0 : 0 < k := by linarith
  have hC1 : 1 ≤ C := by linarith
  have hP : 1 ≤ Cm * k * N1 * Q :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hCm hk) hN1) hQ
  have h1 : 2 * (Cm * k * N1 * Q * c) + 12 * c ≤ 56 * Cm * k * N1 * Q * X := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hP),
      mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ Cm * k * N1 * Q)]
  have hq4 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
  have hq : Q ^ 2 ≤ Nr * Q ^ 4 * Y := by
    have h2 : Q ^ 4 ≤ Nr * Q ^ 4 := le_mul_of_one_le_left (by positivity) hN
    have h3 : Nr * Q ^ 4 ≤ Nr * Q ^ 4 * Y := le_mul_of_one_le_right (by nlinarith) hY
    linarith
  have hCk3 : 0 ≤ C * k ^ 3 := mul_nonneg (by linarith) (by positivity)
  have hb2 : C * k ^ 3 * Q ^ 2 * X ≤ b' := by
    have h4 : C * k ^ 3 * Q ^ 2 * X ≤ C * k ^ 3 * (Nr * Q ^ 4 * Y) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hCk3) hX
    linarith
  have hCLak : 1 ≤ C * La * k :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC1 hLa) hk
  have hW : 0 ≤ N1 * k ^ 2 * Q ^ 2 * X := mul_nonneg (by positivity) hX
  have h2 : 56 * Cm * k * N1 * Q * X * (8 * k * Q) ≤ C * N1 * La * b' := by
    calc 56 * Cm * k * N1 * Q * X * (8 * k * Q) = 448 * Cm * (N1 * k ^ 2 * Q ^ 2 * X) := by ring
      _ ≤ C * (N1 * k ^ 2 * Q ^ 2 * X) := mul_le_mul_of_nonneg_right (by linarith) hW
      _ ≤ (C * La * k) * (C * (N1 * k ^ 2 * Q ^ 2 * X)) :=
          le_mul_of_one_le_left (mul_nonneg (by linarith) hW) hCLak
      _ = C * N1 * La * (C * k ^ 3 * Q ^ 2 * X) := by ring
      _ ≤ C * N1 * La * b' :=
          mul_le_mul_of_nonneg_left hb2 (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  have h3 : 56 * Cm * k * N1 * Q * X ≤ (C * N1 * La / k) * (b' / (2 * Q)) / 4 := by
    rw [show (C * N1 * La / k) * (b' / (2 * Q)) / 4 = (C * N1 * La * b') / (8 * k * Q) by
      field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    exact h2
  have hde0 : 0 ≤ C * N1 * La / k :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) hk0.le
  have hde : C * N1 * La / k ≤ C * N1 * La / k + 2 * Ib / b' :=
    le_add_of_nonneg_right (div_nonneg (by linarith) hb.le)
  have hA0 : 0 ≤ b' / (2 * Q) := div_nonneg hb.le (by linarith)
  have h4 : (C * N1 * La / k) * (b' / (2 * Q)) ≤ (C * N1 * La / k + 2 * Ib / b') * Ai :=
    mul_le_mul hde hAi hA0 (by linarith)
  linarith

theorem share (C k Y M a b' Ib Yb Nr La L : ℝ) (hC : 2 ≤ C) (hk : 2 ≤ k) (hY : 1 ≤ Y)
    (hM0 : 0 ≤ M) (hM : C * k ^ 3 * Y * M ≤ b') (hb : 0 < b') (hYb : 1 ≤ Yb) (hN : 1 ≤ Nr)
    (hLa : 1 ≤ La) (hL : 1 ≤ L) (ha : k * Y ^ 2 * Yb * Nr * La * L ≤ a / b')
    (hIb : Yb * Nr * La * b' / k ≤ Ib) : M * (k * Y / a + 1 / Ib) ≤ 1 / Y := by
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hC0 : 0 < C := by linarith
  have hA : k * Y ^ 2 * Yb * Nr * La * L * b' ≤ a := (le_div_iff₀ hb).mp ha
  have hR : 1 ≤ Y * Yb * Nr * La * L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hY hYb) hN) hLa) hL
  have hR2 : 2 * Y ≤ k * Y ^ 2 * Yb * Nr * La * L := by
    have h1 : 2 * Y ≤ k * Y := by nlinarith
    have h2 : k * Y * 1 ≤ k * Y * (Y * Yb * Nr * La * L) :=
      mul_le_mul_of_nonneg_left hR (by nlinarith)
    linarith
  have ha0 : 0 < a := by nlinarith
  have hCk : 1 ≤ C * k ^ 2 := by nlinarith
  have p1 : M * (k * Y / a) ≤ 1 / (2 * Y) := by
    rw [show M * (k * Y / a) = M * k * Y / a by ring, div_le_div_iff₀ ha0 (by linarith)]
    have e1 : M * k * Y * (2 * Y) * 1 ≤ M * k * Y * (2 * Y) * (C * k ^ 2) :=
      mul_le_mul_of_nonneg_left hCk (by positivity)
    have e2 : C * k ^ 3 * Y * M * (2 * Y) ≤ b' * (2 * Y) := mul_le_mul_of_nonneg_right hM (by linarith)
    have e3 : b' * (2 * Y) ≤ b' * (k * Y ^ 2 * Yb * Nr * La * L) := mul_le_mul_of_nonneg_left hR2 hb.le
    linarith
  have hIb' : Yb * Nr * La * b' ≤ Ib * k := (div_le_iff₀ hk0).mp hIb
  have hYNL : 1 ≤ Yb * Nr * La :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hYb hN) hLa
  have e2 : b' ≤ Yb * Nr * La * b' := le_mul_of_one_le_left hb.le hYNL
  have hIb0 : 0 < Ib := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have p2 : M * (1 / Ib) ≤ 1 / (2 * Y) := by
    rw [show M * (1 / Ib) = M / Ib by ring, div_le_div_iff₀ hIb0 (by linarith)]
    have hCk3 : 0 < C * k ^ 3 := by positivity
    apply le_of_mul_le_mul_right _ hCk3
    have e1 : 2 * b' ≤ C * k ^ 2 * b' := mul_le_mul_of_nonneg_right (by nlinarith) hb.le
    have e3 : C * k ^ 2 * b' ≤ C * k ^ 2 * (Yb * Nr * La * b') := mul_le_mul_of_nonneg_left e2 (by positivity)
    have e4 : C * k ^ 2 * (Yb * Nr * La * b') ≤ C * k ^ 2 * (Ib * k) := mul_le_mul_of_nonneg_left hIb' (by positivity)
    linarith
  have e : 1 / (2 * Y) + 1 / (2 * Y) = 1 / Y := by field_simp; ring
  rw [mul_add]
  linarith

theorem cnkc (C Ck k Y Nr cl b' : ℝ) (hCk : 1 ≤ Ck) (hC : 1000 * Ck ≤ C) (hk : 1 ≤ k) (hY : 1 ≤ Y)
    (hN : 0 ≤ Nr) (hcl : 0 ≤ cl) (hb : 0 < b') (hM : C * k ^ 3 * Y * (Nr * cl) ≤ b') :
    Ck * Nr * k * (2 * cl) / b' ≤ 1 / Y := by
  rw [div_le_div_iff₀ hb (by linarith)]
  have hk3 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have h1 : 2 * Ck * k ≤ C * k ^ 3 := by nlinarith
  have h2 : 2 * Ck * k * (Y * (Nr * cl)) ≤ C * k ^ 3 * (Y * (Nr * cl)) :=
    mul_le_mul_of_nonneg_right h1 (mul_nonneg (by linarith) (mul_nonneg hN hcl))
  linarith

theorem sumP (k Y Yb Nr La L a b' : ℝ) (hk : 1 ≤ k) (hY : 1 ≤ Y) (hYb : 1 ≤ Yb) (hN : 1 ≤ Nr)
    (hLa : 0 ≤ La) (hL : 1 ≤ L) (hb : 0 < b') (ha0 : 0 < a)
    (ha : k * Y ^ 2 * Yb * Nr * La * L ≤ a / b')
    (hexp : Real.exp (-La / 3) ≤ 1 / a) (hYbNa : Yb * Nr ≤ a) :
    ∀ al : ℝ, a ≤ al →
      1 - 2 / (Yb * Nr) ≤ (1 - (k - 1) * (La * b' / k) / al) * (1 - Real.exp (-La / 3)) := by
  intro al hal
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hYb0 : 0 < Yb := by linarith
  have hN0 : 0 < Nr := by linarith
  have hal0 : 0 < al := by linarith
  have hA : k * Y ^ 2 * Yb * Nr * La * L * b' ≤ a := (le_div_iff₀ hb).mp ha
  have hJ0 : 0 ≤ La * b' / k := by positivity
  have hx0 : 0 ≤ (k - 1) * (La * b' / k) / al :=
    div_nonneg (mul_nonneg (by linarith) hJ0) hal0.le
  have hx : (k - 1) * (La * b' / k) / al ≤ 1 / (Yb * Nr) := by
    rw [div_le_div_iff₀ hal0 (by positivity)]
    have e0 : k * (La * b' / k) = La * b' := by field_simp
    have e1 : (k - 1) * (La * b' / k) ≤ La * b' := by linarith
    have e2 : (k - 1) * (La * b' / k) * (Yb * Nr) ≤ La * b' * (Yb * Nr) :=
      mul_le_mul_of_nonneg_right e1 (by positivity)
    have h1 : 1 ≤ k * Y ^ 2 * L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk (one_le_pow₀ hY)) hL
    have e3 : La * b' * (Yb * Nr) ≤ La * b' * (Yb * Nr) * (k * Y ^ 2 * L) :=
      le_mul_of_one_le_right (by positivity) h1
    linarith
  have hy0 : 0 ≤ Real.exp (-La / 3) := (Real.exp_pos _).le
  have hy : Real.exp (-La / 3) ≤ 1 / (Yb * Nr) :=
    le_trans hexp (one_div_le_one_div_of_le (by positivity) hYbNa)
  have e : 2 / (Yb * Nr) = 2 * (1 / (Yb * Nr)) := by ring
  nlinarith [mul_nonneg hx0 hy0]

theorem half (Yb : ℝ) (N : ℕ) (hYb : 4 ≤ Yb) (hN : 1 ≤ N) :
    1 / 2 ≤ (1 - 2 / (Yb * N)) ^ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hYb0 : 0 < Yb := by linarith
  have h2 : 2 / (Yb * N) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have key := one_add_mul_le_pow (a := -(2 / (Yb * N))) (by linarith) N
  have e1 : (N : ℝ) * (-(2 / (Yb * N))) = -(2 / Yb) := by field_simp
  have e2 : 2 / Yb ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hYb0 (by norm_num)]
    linarith
  rw [show (1 : ℝ) - 2 / (Yb * N) = 1 + -(2 / (Yb * N)) by ring]
  linarith

end ParamsIProof

end Formalism.CountingSumsFrames

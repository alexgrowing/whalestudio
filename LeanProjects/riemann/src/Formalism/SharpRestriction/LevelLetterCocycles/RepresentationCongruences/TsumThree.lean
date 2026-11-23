import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.InvSubOneSqLeInv

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

def Sg (l h w S η : ℕ) : ℝ :=
  (h : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + S + η) / l + Real.logb l (2 * (h : ℝ)) + 1

def cW (l H : ℕ) : ℕ := ⌈1 + Real.logb l ((H : ℝ) + 1)⌉₊

private theorem reciprocal_bounds_of_eleven_le {L x y z : ℝ} (hL : 11 ≤ L) (hx : x = L⁻¹) (hy : y = (L - 1)⁻¹)
    (hz : z = (L - 2)⁻¹) :
    L * x = 1 ∧ L * y = 1 + y ∧ (L - 2) * z = 1 ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
    x ≤ 1 / 11 ∧ y ≤ 1 / 10 ∧ z ≤ 1 / 9 ∧ y ≤ 11 / 10 * x ∧ z ≤ 11 / 9 * x ∧
    y = x + x * y := by
  subst hx hy hz
  have h0 : (0:ℝ) < L := by linarith
  have h1 : (0:ℝ) < L - 1 := by linarith
  have h2 : (0:ℝ) < L - 2 := by linarith
  have e0 : L * L⁻¹ = 1 := mul_inv_cancel₀ h0.ne'
  have e1 : (L - 1) * (L - 1)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
  have e2 : (L - 2) * (L - 2)⁻¹ = 1 := mul_inv_cancel₀ h2.ne'
  have p0 : 0 < L⁻¹ := inv_pos.mpr h0
  have p1 : 0 < (L - 1)⁻¹ := inv_pos.mpr h1
  have p2 : 0 < (L - 2)⁻¹ := inv_pos.mpr h2
  have q0 : L⁻¹ ≤ 1 / 11 := by nlinarith [mul_le_mul_of_nonneg_left hL p0.le]
  have q1 : (L - 1)⁻¹ ≤ 1 / 10 := by
    nlinarith [mul_le_mul_of_nonneg_left (show (10:ℝ) ≤ L - 1 by linarith) p1.le]
  have q2 : (L - 2)⁻¹ ≤ 1 / 9 := by
    nlinarith [mul_le_mul_of_nonneg_left (show (9:ℝ) ≤ L - 2 by linarith) p2.le]
  have iy : (L - 1)⁻¹ = L⁻¹ + L⁻¹ * (L - 1)⁻¹ := by
    linear_combination (-(L - 1)⁻¹) * e0 + L⁻¹ * e1
  have iz : (L - 2)⁻¹ = L⁻¹ + 2 * (L⁻¹ * (L - 2)⁻¹) := by
    linear_combination (-(L - 2)⁻¹) * e0 + L⁻¹ * e2
  refine ⟨e0, by linear_combination e1, e2, p0, p1, p2, q0, q1, q2, ?_, ?_, iy⟩
  · nlinarith [mul_le_mul_of_nonneg_left q1 p0.le]
  · nlinarith [mul_le_mul_of_nonneg_left q2 p0.le]

theorem tsum_three (l : ℕ) (hl : 11 ≤ l) (f : ℕ → ℝ) (x₀ x₁ X : ℝ) (hf : ∀ a, 0 ≤ f a)
    (h0 : f 0 ≤ x₀) (h1 : f 1 ≤ x₁) (h2 : ∀ a, 2 ≤ a → f a ≤ X) :
    ∑' a : ℕ, f a * ((l : ℝ) - 1) ^ (-(a : ℤ)) ≤
      x₀ + x₁ / ((l : ℝ) - 1) + X / (((l : ℝ) - 1) * ((l : ℝ) - 2)) := by
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (l:ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((l:ℝ) - 1)⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ((l:ℝ) - 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨eLx, eLy, eLz, px, py, pz, hx1, hy1, hz1, hyx, hzx, iy⟩ := reciprocal_bounds_of_eleven_le hL hx hy hz
  have hyl : y < 1 := by linarith
  have hterm : ∀ a : ℕ, f a * ((l : ℝ) - 1) ^ (-(a : ℤ)) = f a * y ^ a := by
    intro a
    rw [zpow_neg, zpow_natCast, hy, inv_pow]
  have hpt : ∀ i : ℕ, f i * y ^ i ≤
      X * y ^ i + ((if i = 0 then x₀ - X else 0) + (if i = 1 then (x₁ - X) * y else 0)) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      simp
      linarith
    · by_cases hi1 : i = 1
      · subst hi1
        simp
        nlinarith [mul_le_mul_of_nonneg_right h1 py.le]
      · rw [if_neg hi0, if_neg hi1, add_zero, add_zero]
        exact mul_le_mul_of_nonneg_right (h2 i (by omega)) (pow_nonneg py.le i)
  have H := ((hasSum_geometric_of_lt_one py.le hyl).mul_left X).add
    ((hasSum_ite_eq (0:ℕ) (x₀ - X)).add (hasSum_ite_eq (1:ℕ) ((x₁ - X) * y)))
  have hfs : Summable (fun i : ℕ => f i * y ^ i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hf i) (pow_nonneg py.le i)) hpt H.summable
  have hzy : z - y = y * z := by linear_combination (-z) * eLy + y * eLz
  have e1 : (1 - y)⁻¹ = 1 + z := inv_eq_of_mul_eq_one_right (by linear_combination hzy)
  have c1 : x₁ / ((l : ℝ) - 1) = x₁ * y := by rw [hy, div_eq_mul_inv]
  have c2 : X / (((l : ℝ) - 1) * ((l : ℝ) - 2)) = X * (y * z) := by
    rw [hy, hz, div_eq_mul_inv, mul_inv]
  calc ∑' a : ℕ, f a * ((l : ℝ) - 1) ^ (-(a : ℤ)) = ∑' a : ℕ, f a * y ^ a := tsum_congr hterm
    _ ≤ X * (1 - y)⁻¹ + ((x₀ - X) + (x₁ - X) * y) := hasSum_le hpt hfs.hasSum H
    _ = x₀ + x₁ / ((l : ℝ) - 1) + X / (((l : ℝ) - 1) * ((l : ℝ) - 2)) := by
      rw [e1, c1, c2]
      linear_combination X * hzy

theorem cW_le (l : ℕ) (hl : 11 ≤ l) (h η H : ℕ) (hη : η + 1 ≤ h) (hH : H ≤ h + η) :
    (cW l H : ℝ) ≤ 2 + Real.logb l (2 * (h : ℝ)) := by
  have hL : (1:ℝ) < l := by
    have : (11:ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hH1 : (H:ℝ) + 1 ≤ 2 * (h:ℝ) := by
    have : H + 1 ≤ 2 * h := by omega
    exact_mod_cast this
  have hpos : (0:ℝ) < (H:ℝ) + 1 := by positivity
  have hlog0 : 0 ≤ Real.logb l ((H:ℝ) + 1) :=
    Real.logb_nonneg hL (by linarith [(Nat.cast_nonneg H : (0:ℝ) ≤ H)])
  have hmono : Real.logb l ((H:ℝ) + 1) ≤ Real.logb l (2 * (h:ℝ)) := by
    first
      | exact Real.logb_le_logb_of_le hL hpos hH1
      | exact (Real.logb_le_logb hL hpos (by linarith)).mpr hH1
  have hc := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 1 + Real.logb l ((H:ℝ) + 1) by linarith)
  unfold cW
  linarith

private theorem reciprocal_product_bounds_of_eleven_le {x y z : ℝ} (px : 0 < x) (py : 0 < y) (pz : 0 < z) (hx1 : x ≤ 1 / 11)
    (hy1 : y ≤ 1 / 10) (hz1 : z ≤ 1 / 9) (hyx : y ≤ 11 / 10 * x) (hzx : z ≤ 11 / 9 * x) :
    x ^ 2 ≤ x / 11 ∧ x * y ≤ 11 / 10 * x ^ 2 ∧ y + y ^ 2 ≤ 121 / 100 * x ∧ y + y ^ 2 ≤ 11 / 100 ∧
    z * (y + y ^ 2) ≤ 3 / 2 * x ^ 2 ∧ z * (y + y ^ 2) ≤ 11 / 900 ∧ y ^ 2 ≤ 121 / 100 * x ^ 2 ∧
    y ^ 2 ≤ 1 / 100 ∧ y ^ 2 * z ≤ 121 / 900 * x ^ 2 ∧ y ^ 2 * z ≤ 1 / 900 ∧
    z * y ≤ 121 / 90 * x ^ 2 ∧ z * y ≤ 1 / 90 := by
  have a1 : x ^ 2 ≤ x / 11 := by nlinarith [mul_le_mul_of_nonneg_left hx1 px.le]
  have a2 : x * y ≤ 11 / 10 * x ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hyx px.le]
  have hyy := mul_le_mul_of_nonneg_left hy1 py.le
  have a3 : y + y ^ 2 ≤ 121 / 100 * x := by nlinarith
  have a4 : y + y ^ 2 ≤ 11 / 100 := by nlinarith
  have hP0 : 0 ≤ y + y ^ 2 := add_nonneg py.le (sq_nonneg y)
  have a5 : z * (y + y ^ 2) ≤ 3 / 2 * x ^ 2 := by
    have := mul_le_mul hzx a3 hP0 (by linarith : (0:ℝ) ≤ 11 / 9 * x)
    nlinarith [sq_nonneg x]
  have a6 : z * (y + y ^ 2) ≤ 11 / 900 := by
    have := mul_le_mul hz1 a4 hP0 (by norm_num : (0:ℝ) ≤ 1 / 9)
    linarith
  have a7 : y ^ 2 ≤ 121 / 100 * x ^ 2 := by
    have := mul_le_mul hyx hyx py.le (by linarith : (0:ℝ) ≤ 11 / 10 * x)
    nlinarith
  have a8 : y ^ 2 ≤ 1 / 100 := by nlinarith
  have a9 : y ^ 2 * z ≤ 121 / 900 * x ^ 2 := by
    have := mul_le_mul a7 hz1 pz.le (by positivity : (0:ℝ) ≤ 121 / 100 * x ^ 2)
    linarith
  have a10 : y ^ 2 * z ≤ 1 / 900 := by
    have := mul_le_mul a8 hz1 pz.le (by norm_num : (0:ℝ) ≤ 1 / 100)
    linarith
  have a11 : z * y ≤ 121 / 90 * x ^ 2 := by
    have := mul_le_mul hzx hyx py.le (by linarith : (0:ℝ) ≤ 11 / 9 * x)
    nlinarith
  have a12 : z * y ≤ 1 / 90 := by
    have := mul_le_mul hz1 hy1 py.le (by norm_num : (0:ℝ) ≤ 1 / 9)
    linarith
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩

private theorem logb_two_mul_natCast_nonneg_of_eleven_le (l n : ℕ) (hl : 11 ≤ l) : 0 ≤ Real.logb l (2 * (n : ℝ)) := by
  have hL : (1:ℝ) < l := by
    have : (11:ℝ) ≤ l := by exact_mod_cast hl
    linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · apply Real.logb_nonneg hL
    have : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    linarith

private theorem mul_div_sub_one_sq_eq_mul_add_sq (v L y : ℝ) (hy : y = (L - 1)⁻¹) (eLy : L * y = 1 + y) :
    v * L / (L - 1) ^ 2 = v * (y + y ^ 2) := by
  have key : L * y ^ 2 = y + y ^ 2 := by linear_combination y * eLy
  rw [← key, hy, inv_pow]
  ring

set_option maxHeartbeats 800000 in

theorem rr_le (l : ℕ) (hl : 11 ≤ l) (h w S η H H₁ : ℕ) (hη : η + 1 ≤ h)
    (hH : H ≤ h + η) (hH₁ : H₁ ≤ w + S + η) (s r : ℝ)
    (hs : s ≤ ((H₁ : ℝ) + cW l H + 3) + ((H : ℝ) + cW l H + 3) / ((l : ℝ) - 2))
    (hr : r ≤ s * l / ((l : ℝ) - 1) ^ 2 + cW l H) :
    r ≤ 2 * ((w : ℝ) + S + η) / l + 2 * (h : ℝ) / (l : ℝ) ^ 2 + 2 * Real.logb l (2 * (h : ℝ)) + 3 ∧
    2 * ((w : ℝ) + S + η) / l + 2 * (h : ℝ) / (l : ℝ) ^ 2 + 2 * Real.logb l (2 * (h : ℝ)) + 3 ≤
      3 * Sg l h w S η := by
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (l:ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((l:ℝ) - 1)⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ((l:ℝ) - 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨eLx, eLy, eLz, px, py, pz, hx1, hy1, hz1, hyx, hzx, iy⟩ := reciprocal_bounds_of_eleven_le hL hx hy hz
  obtain ⟨hx2, -, hP1, hP2, hzP1, hzP2, -⟩ := reciprocal_product_bounds_of_eleven_le px py pz hx1 hy1 hz1 hyx hzx
  have cw1 : ((w:ℝ) + S + η) / l = ((w:ℝ) + S + η) * x := by rw [hx, div_eq_mul_inv]
  have ch1 : (h:ℝ) / (l:ℝ) ^ 2 = (h:ℝ) * x ^ 2 := by rw [hx, inv_pow, div_eq_mul_inv]
  have n1 : 0 ≤ (w:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n2 : 0 ≤ (S:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n3 : 0 ≤ (η:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n4 : 0 ≤ (h:ℝ) * x ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg x)
  have hc := cW_le l hl h η H hη hH
  have hg := logb_two_mul_natCast_nonneg_of_eleven_le l h hl
  rw [mul_div_sub_one_sq_eq_mul_add_sq _ _ _ hy eLy] at hr
  have ez : ((H : ℝ) + cW l H + 3) / ((l : ℝ) - 2) = ((H : ℝ) + cW l H + 3) * z := by
    rw [hz, div_eq_mul_inv]
  rw [ez] at hs
  have cw : 2 * ((w:ℝ) + S + η) / l = 2 * ((w:ℝ) + S + η) * x := by rw [hx, div_eq_mul_inv]
  have ch : 2 * (h:ℝ) / (l:ℝ) ^ 2 = 2 * (h:ℝ) * x ^ 2 := by rw [hx, inv_pow, div_eq_mul_inv]
  have hP0 : 0 ≤ y + y ^ 2 := add_nonneg py.le (sq_nonneg y)
  have hzP0 : 0 ≤ z * (y + y ^ 2) := mul_nonneg pz.le hP0
  have hH1r : (H₁:ℝ) ≤ (w:ℝ) + S + η := by exact_mod_cast hH₁
  have hHr : (H:ℝ) ≤ (h:ℝ) + η := by exact_mod_cast hH
  have hu0 : (0:ℝ) ≤ (w:ℝ) + S + η := by positivity
  have hc3 : (0:ℝ) ≤ (cW l H : ℝ) + 3 := by positivity
  have b1 := mul_le_mul hH1r hP1 hP0 hu0
  have b2 := mul_le_mul_of_nonneg_left hP2 hc3
  have b3 := mul_le_mul hHr hzP1 hzP0 (by positivity : (0:ℝ) ≤ (h:ℝ) + η)
  have b4 := mul_le_mul_of_nonneg_left hzP2 hc3
  have hsP := mul_le_mul_of_nonneg_right hs hP0
  have b5 := mul_le_mul_of_nonneg_left hx2 (Nat.cast_nonneg η : (0:ℝ) ≤ η)
  unfold Sg
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

theorem sig_le (l : ℕ) (hl : 11 ≤ l) (h w S η : ℕ) (h1 : 1 ≤ h) (hG : w + S ≤ h) :
    (⌈((2 * (w + S) : ℕ) + ((2 * h / (l - 1) + 1 : ℕ) : ℝ)) * l / ((l : ℝ) - 1) ^ 2 + 1⌉₊ : ℝ) ≤
      3 * Sg l h w S η := by
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (l:ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((l:ℝ) - 1)⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ((l:ℝ) - 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨eLx, eLy, eLz, px, py, pz, hx1, hy1, hz1, hyx, hzx, iy⟩ := reciprocal_bounds_of_eleven_le hL hx hy hz
  have cw1 : ((w:ℝ) + S + η) / l = ((w:ℝ) + S + η) * x := by rw [hx, div_eq_mul_inv]
  have ch1 : (h:ℝ) / (l:ℝ) ^ 2 = (h:ℝ) * x ^ 2 := by rw [hx, inv_pow, div_eq_mul_inv]
  have n1 : 0 ≤ (w:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n2 : 0 ≤ (S:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n3 : 0 ≤ (η:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n4 : 0 ≤ (h:ℝ) * x ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg x)
  have hx2 : x ^ 2 ≤ x / 11 := by nlinarith [mul_le_mul_of_nonneg_left hx1 px.le]
  have hg := logb_two_mul_natCast_nonneg_of_eleven_le l h hl
  have hl1 : ((l - 1 : ℕ) : ℝ) = (l:ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ l by omega), Nat.cast_one]
  have hm : ((2 * h / (l - 1) : ℕ) : ℝ) ≤ 2 * (h:ℝ) * y := by
    calc ((2 * h / (l - 1) : ℕ) : ℝ) ≤ ((2 * h : ℕ) : ℝ) / ((l - 1 : ℕ) : ℝ) := Nat.cast_div_le
      _ = 2 * (h:ℝ) * y := by
        rw [hl1, hy, div_eq_mul_inv]
        push_cast <;> ring
  have e1 : ((2 * (w + S) : ℕ) : ℝ) = 2 * ((w:ℝ) + S) := by push_cast <;> ring
  have e2 : ((2 * h / (l - 1) + 1 : ℕ) : ℝ) = ((2 * h / (l - 1) : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  refine le_trans (Nat.ceil_lt_add_one ?_).le ?_
  · positivity
  rw [mul_div_sub_one_sq_eq_mul_add_sq _ _ _ hy eLy]
  have hP0 : 0 ≤ y + y ^ 2 := add_nonneg py.le (sq_nonneg y)
  have hP1 : y + y ^ 2 ≤ 121 / 100 * x := by nlinarith [mul_le_mul_of_nonneg_left hy1 py.le]
  have hhy : 0 ≤ (h:ℝ) * y := mul_nonneg (Nat.cast_nonneg _) py.le
  have hV : ((2 * (w + S) : ℕ) : ℝ) + ((2 * h / (l - 1) + 1 : ℕ) : ℝ) ≤
      2 * ((w:ℝ) + S) + 2 * (h:ℝ) * y + 1 := by
    rw [e1, e2]
    linarith
  have hV0 : (0:ℝ) ≤ 2 * ((w:ℝ) + S) + 2 * (h:ℝ) * y + 1 := by
    have hw0 : (0:ℝ) ≤ w := Nat.cast_nonneg _
    have hS0 : (0:ℝ) ≤ S := Nat.cast_nonneg _
    linarith
  have b1 := mul_le_mul hV hP1 hP0 hV0
  have hxy : x * y ≤ 11 / 10 * x ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hyx px.le]
  have b2 := mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg h : (0:ℝ) ≤ h)
  unfold Sg
  linarith

set_option maxHeartbeats 800000 in

theorem Aa_cut_le (l : ℕ) (hl : 11 ≤ l) (h w S η H H₁ H₂ : ℕ) (hη : η + 1 ≤ h)
    (hH : H ≤ h + η) (hH₁ : H₁ ≤ h + η) (hH₂ : H₂ ≤ w + S + η) (s A : ℝ)
    (hs : s ≤ ((H₁ : ℝ) + cW l H + 3) + ((H₂ : ℝ) + cW l H + 3) / ((l : ℝ) - 1) +
      ((H : ℝ) + cW l H + 3) / (((l : ℝ) - 1) * ((l : ℝ) - 2)))
    (hA : A ≤ s / ((l : ℝ) - 1) + 1) :
    A ≤ (H₁ : ℝ) / l + 2 * Sg l h w S η := by
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (l:ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((l:ℝ) - 1)⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ((l:ℝ) - 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨eLx, eLy, eLz, px, py, pz, hx1, hy1, hz1, hyx, hzx, iy⟩ := reciprocal_bounds_of_eleven_le hL hx hy hz
  obtain ⟨hx2, hxy, -, -, -, -, hy2, hy2', hy2z, hy2z', -⟩ :=
    reciprocal_product_bounds_of_eleven_le px py pz hx1 hy1 hz1 hyx hzx
  have cw1 : ((w:ℝ) + S + η) / l = ((w:ℝ) + S + η) * x := by rw [hx, div_eq_mul_inv]
  have ch1 : (h:ℝ) / (l:ℝ) ^ 2 = (h:ℝ) * x ^ 2 := by rw [hx, inv_pow, div_eq_mul_inv]
  have n1 : 0 ≤ (w:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n2 : 0 ≤ (S:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n3 : 0 ≤ (η:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n4 : 0 ≤ (h:ℝ) * x ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg x)
  have hc := cW_le l hl h η H hη hH
  have hg := logb_two_mul_natCast_nonneg_of_eleven_le l h hl
  have c1 : (H₁:ℝ) / l = (H₁:ℝ) * x := by rw [hx, div_eq_mul_inv]
  have hH1r : (H₁:ℝ) ≤ (h:ℝ) + η := by exact_mod_cast hH₁
  have hHr : (H:ℝ) ≤ (h:ℝ) + η := by exact_mod_cast hH
  have hhη : (0:ℝ) ≤ (h:ℝ) + η := by positivity
  have hu0 : (0:ℝ) ≤ (w:ℝ) + S + η := by positivity
  have hc3 : (0:ℝ) ≤ (cW l H : ℝ) + 3 := by positivity
  have d0 : (H₁:ℝ) * y = (H₁:ℝ) * x + (H₁:ℝ) * (x * y) := by linear_combination (H₁:ℝ) * iy
  have d1 := mul_le_mul hH1r hxy (mul_nonneg px.le py.le) hhη
  have d2 := mul_le_mul_of_nonneg_left hy1 hc3
  have d7 := mul_le_mul_of_nonneg_left hx2 (Nat.cast_nonneg η : (0:ℝ) ≤ η)
  have d8 := mul_le_mul_of_nonneg_left hx2 hu0
  have e3 : s / ((l : ℝ) - 1) = s * y := by rw [hy, div_eq_mul_inv]
  rw [e3] at hA
  have e1 : ((H₂ : ℝ) + cW l H + 3) / ((l : ℝ) - 1) = ((H₂ : ℝ) + cW l H + 3) * y := by
    rw [hy, div_eq_mul_inv]
  have e2 : ((H : ℝ) + cW l H + 3) / (((l : ℝ) - 1) * ((l : ℝ) - 2)) =
      ((H : ℝ) + cW l H + 3) * (y * z) := by
    rw [hy, hz, div_eq_mul_inv, mul_inv]
  rw [e1, e2] at hs
  have hsy := mul_le_mul_of_nonneg_right hs py.le
  have hH2r : (H₂:ℝ) ≤ (w:ℝ) + S + η := by exact_mod_cast hH₂
  have d3 := mul_le_mul hH2r hy2 (sq_nonneg y) hu0
  have d4 := mul_le_mul_of_nonneg_left hy2' hc3
  have d5 := mul_le_mul hHr hy2z (mul_nonneg (sq_nonneg y) pz.le) hhη
  have d6 := mul_le_mul_of_nonneg_left hy2z' hc3
  unfold Sg
  linarith

set_option maxHeartbeats 800000 in

theorem Aa_le (l : ℕ) (hl : 11 ≤ l) (h w S η H H₁ : ℕ) (hη : η + 1 ≤ h)
    (hH : H ≤ h + η) (hH₁ : H₁ ≤ h + η) (s A : ℝ)
    (hs : s ≤ ((H₁ : ℝ) + cW l H + 3) + ((H : ℝ) + cW l H + 3) / ((l : ℝ) - 2))
    (hA : A ≤ s / ((l : ℝ) - 1) + 1) :
    A ≤ (H₁ : ℝ) / l + 5 / 2 * Sg l h w S η := by
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (l:ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((l:ℝ) - 1)⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ((l:ℝ) - 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨eLx, eLy, eLz, px, py, pz, hx1, hy1, hz1, hyx, hzx, iy⟩ := reciprocal_bounds_of_eleven_le hL hx hy hz
  obtain ⟨hx2, hxy, -, -, -, -, -, -, -, -, hzy, hzy'⟩ :=
    reciprocal_product_bounds_of_eleven_le px py pz hx1 hy1 hz1 hyx hzx
  have cw1 : ((w:ℝ) + S + η) / l = ((w:ℝ) + S + η) * x := by rw [hx, div_eq_mul_inv]
  have ch1 : (h:ℝ) / (l:ℝ) ^ 2 = (h:ℝ) * x ^ 2 := by rw [hx, inv_pow, div_eq_mul_inv]
  have n1 : 0 ≤ (w:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n2 : 0 ≤ (S:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n3 : 0 ≤ (η:ℝ) * x := mul_nonneg (Nat.cast_nonneg _) px.le
  have n4 : 0 ≤ (h:ℝ) * x ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg x)
  have hc := cW_le l hl h η H hη hH
  have hg := logb_two_mul_natCast_nonneg_of_eleven_le l h hl
  have c1 : (H₁:ℝ) / l = (H₁:ℝ) * x := by rw [hx, div_eq_mul_inv]
  have hH1r : (H₁:ℝ) ≤ (h:ℝ) + η := by exact_mod_cast hH₁
  have hHr : (H:ℝ) ≤ (h:ℝ) + η := by exact_mod_cast hH
  have hhη : (0:ℝ) ≤ (h:ℝ) + η := by positivity
  have hu0 : (0:ℝ) ≤ (w:ℝ) + S + η := by positivity
  have hc3 : (0:ℝ) ≤ (cW l H : ℝ) + 3 := by positivity
  have d0 : (H₁:ℝ) * y = (H₁:ℝ) * x + (H₁:ℝ) * (x * y) := by linear_combination (H₁:ℝ) * iy
  have d1 := mul_le_mul hH1r hxy (mul_nonneg px.le py.le) hhη
  have d2 := mul_le_mul_of_nonneg_left hy1 hc3
  have d7 := mul_le_mul_of_nonneg_left hx2 (Nat.cast_nonneg η : (0:ℝ) ≤ η)
  have d8 := mul_le_mul_of_nonneg_left hx2 hu0
  have e3 : s / ((l : ℝ) - 1) = s * y := by rw [hy, div_eq_mul_inv]
  rw [e3] at hA
  have ez : ((H : ℝ) + cW l H + 3) / ((l : ℝ) - 2) = ((H : ℝ) + cW l H + 3) * z := by
    rw [hz, div_eq_mul_inv]
  rw [ez] at hs
  have hsy := mul_le_mul_of_nonneg_right hs py.le
  have d5 := mul_le_mul hHr hzy (mul_nonneg pz.le py.le) hhη
  have d6 := mul_le_mul_of_nonneg_left hzy' hc3
  unfold Sg
  linarith

theorem A_le (l : ℕ) (hl : 11 ≤ l) (h η H : ℕ) (hH : H ≤ h + η) (A : ℝ)
    (hA : A ≤ (H : ℝ) / ((l : ℝ) - 1) + 1) :
    A ≤ ((h : ℝ) + η) / ((l : ℝ) - 1) + 1 := by
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (0:ℝ) < (l:ℝ) - 1 := by linarith
  have hHr : (H:ℝ) ≤ (h:ℝ) + η := by exact_mod_cast hH
  have e1 : (H:ℝ) / ((l:ℝ) - 1) = (H:ℝ) * ((l:ℝ) - 1)⁻¹ := div_eq_mul_inv _ _
  have e2 : ((h:ℝ) + η) / ((l:ℝ) - 1) = ((h:ℝ) + η) * ((l:ℝ) - 1)⁻¹ := div_eq_mul_inv _ _
  have p : (0:ℝ) ≤ ((l:ℝ) - 1)⁻¹ := inv_nonneg.mpr h1.le
  have := mul_le_mul_of_nonneg_right hHr p
  linarith

private theorem mul_two_mul_sub_one_div_sq_eq (v L y : ℝ) (hy : y = (L - 1)⁻¹)
    (eLy : L * y = 1 + y) : v * (2 * L - 1) / (L - 1) ^ 2 = v * (2 * y + y ^ 2) := by
  have key : (2 * L - 1) * y ^ 2 = 2 * y + y ^ 2 := by linear_combination (2 * y) * eLy
  rw [← key, hy, inv_pow]
  ring

theorem K6 (l : ℕ) (hl : 11 ≤ l) (b w S η H : ℕ) (hηb : 20 * η ≤ b) (hSb : 20 * S ≤ b)
    (hwb : 20 * w ≤ b) (hH : H ≤ b + 2 * η + S)
    (hsm : 40 * Sg l (b + η + S) w S η ≤ (b : ℝ) / 4) (a : ℕ)
    (ha : (a : ℝ) ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cW l H + 1) :
    2 * a + η + 1 ≤ b := by
  have hL : (11:ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (l:ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((l:ℝ) - 1)⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ((l:ℝ) - 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨eLx, eLy, eLz, px, py, pz, hx1, hy1, hz1, hyx, hzx, iy⟩ := reciprocal_bounds_of_eleven_le hL hx hy hz
  have hg' := logb_two_mul_natCast_nonneg_of_eleven_le l (b + η + S) hl
  have t1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (l:ℝ) ^ 2 := by positivity
  have t2 : 0 ≤ ((w:ℝ) + S + η) / l := by positivity
  unfold Sg at hsm
  have hb160 : (160:ℝ) ≤ b := by linarith
  have hb1 : 1 ≤ b := by exact_mod_cast (show (1:ℝ) ≤ b by linarith)
  have hc := cW_le l hl (b + η + S) η H (by omega) (by omega)
  have hfrac : (H:ℝ) * (2 * l - 1) / ((l:ℝ) - 1) ^ 2 ≤ (H:ℝ) * (21 / 100) := by
    rw [mul_two_mul_sub_one_div_sq_eq _ _ _ hy eLy]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hy1 py.le]
  have hHr : (H:ℝ) ≤ b + 2 * η + S := by exact_mod_cast hH
  have hηr : 20 * (η:ℝ) ≤ b := by exact_mod_cast hηb
  have hSr : 20 * (S:ℝ) ≤ b := by exact_mod_cast hSb
  have key : 2 * (a:ℝ) + η + 1 ≤ b := by linarith
  exact_mod_cast key

end Formalism.MainNotions.N.FrobeniusPowerSeries

import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ReflectionMemGlevCastSucc

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem threshold_arith_letter_case (k Ns c q bo : ℝ) (hk5 : 5 ≤ k) (hN : 1 ≤ Ns) (hc : 40 * (k * Ns) ≤ c) (hq : 9 / 10 * c ≤ q)
    (hb : q - k < bo) : c / 2 ≤ 2 / 3 * bo - k * Ns := by
  have hkN : k ≤ k * Ns := by nlinarith
  linarith

theorem threshold_arith_w_case (k Ns c q fl r : ℝ) (hk5 : 5 ≤ k) (hN : 1 ≤ Ns) (hr : r ≤ k) (hc : 40 * (k * Ns) ≤ c)
    (hq : 9 / 10 * c ≤ q) (hfl : q - 1 < fl) :
    c / 2 ≤ 2 / 3 * (fl - (k + r + 1) - (k * Ns + 1)) - k * Ns := by
  have hkN : k ≤ k * Ns := by nlinarith
  linarith

theorem natDiv_gt (n m : ℕ) (hm : 0 < m) : (n : ℝ) / (m : ℝ) - 1 < ((n / m : ℕ) : ℝ) := by
  have h := Nat.div_add_mod n m
  have hr := Nat.mod_lt n hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have e1 : (n : ℝ) = (m : ℝ) * ((n / m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) := by exact_mod_cast h.symm
  have e2 : ((n % m : ℕ) : ℝ) < m := by exact_mod_cast hr
  rw [div_sub_one hm'.ne', div_lt_iff₀ hm']
  linarith

theorem threshold_power_bound_of_counts (C₀ : ℝ) (h41 : TopCountLowerBounds C₀) (hOld : OldestLetterInSegment) : ThresholdPowerLowerBound C₀ := by
  unfold ThresholdPowerLowerBound
  intro p n' r K _ _ _ X hX hC1 hC2 j bb hS x hx
  have b0 := basics hX
  have hO := hOld p n' r K X hX j x hx
  have hob := mem_letters_bounds hO.1
  have h41' := (h41 p n' r K X hX hC1 hC2).1 _ hob.2.2
  have hdeg := (hX.degs _ hob.2.2).1
  have hk : Dat.k (r := r) K = ((r : ℝ) + (K : ℝ)) := by unfold Dat.k; push_cast; rfl
  have hk5 : (5 : ℝ) ≤ ((r : ℝ) + (K : ℝ)) := hk ▸ b0.k5
  have hN := b0.Ns1
  have hY := b0.Y1
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := b0.p1.le
  have hRT := pow_Rj_le hX j
  have hRp : (0 : ℝ) ≤ (p : ℝ) ^ (X.Rj p K j) := by positivity
  have hTp : (0 : ℝ) ≤ Tj X p K j := hRp.trans hRT
  have hden := den_pos hX j
  have hTa : 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j = X.a := by
    rw [← hk]
    unfold Tj
    exact mul_div_cancel₀ _ hden.ne'
  have hEW : (X.F.dist j (X.F.oldest j x)) ≤ (X.F.dist j (X.F.fr (j - 1) 0)) := by
    unfold Frames.dist
    omega
  have hPe : (p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) ≤ (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) := pow_le_pow_right₀ hP1 hEW
  have hDpos : 0 < ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) := by positivity
  have hc : 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) ≤ (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by
    rw [le_div_iff₀ hDpos, pow_add]
    have hkN : 0 ≤ ((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ) := by positivity
    have h40 : (40 : ℝ) ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) := by nlinarith
    have h1 : 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right h40 hkN]
    have hq0 : 0 ≤ (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j := by positivity
    calc 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) * ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) * (p : ℝ) ^ (X.Rj p K j))
        ≤ 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) * ((p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hPe hRT hRp (by positivity)) (by positivity)
      _ ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j) := mul_le_mul_of_nonneg_right h1 hq0
      _ = X.a := by rw [← hTa]; ring
      _ ≤ ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) := hdeg
  have hq : 9 / 10 * (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) ≤ (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by
    calc 9 / 10 * (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) = (9 / 10 * ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ)) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) := by ring
      _ ≤ (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by gcongr
  have hsplit : ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / (p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) / 2 = (p : ℝ) ^ (X.Rj p K j) * ((((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) / 2) := by
    rw [pow_add]
    field_simp
  unfold Dat.th Dat.Bo Dat.thc
  rw [hsplit]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ hRp
  split_ifs with hW
  · have hfl := natDiv_gt (X.a' p K (posOf n' (X.F.oldest j x))) (p ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) (pow_pos (by have := hX.p13; omega) _)
    push_cast at hfl
    have := threshold_arith_w_case ((r : ℝ) + (K : ℝ)) (X.Ns : ℝ) (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) _ (r : ℝ) hk5 hN (by linarith) hc hq hfl
    unfold Dat.Bw Dat.m0
    push_cast
    have hcast : ((((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℤ) / ((p : ℤ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) : ℤ) : ℝ) = (((X.a' p K (posOf n' (X.F.oldest j x))) / p ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, ← Int.natCast_div, Int.cast_natCast]
    rw [hcast]
    linarith
  · have hb := hS _ (hO.2 hW)
    rw [hk] at hb
    have := threshold_arith_letter_case ((r : ℝ) + (K : ℝ)) (X.Ns : ℝ) (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) _ hk5 hN hc hq hb
    linarith

theorem order_numeric_bound_of_oldest (C₀ : ℝ) (hOld : OldestLetterInSegment) : OrderNumericBound C₀ := by
  unfold OrderNumericBound
  intro p n' r K _ _ _ X hX _ _ j x hx
  have b := basics hX
  have hO := hOld p n' r K X hX j x hx
  simp only [Dat.toLate, Finset.mem_filter] at hx
  have hxb := mem_letters_bounds hx.1
  have hob := mem_letters_bounds hO.1
  have hL : (X.L₁ : ℤ) < x - X.F.oldest j x := hX.valid.2.2.2.2.2.2.2.2 j x hx.1 hx.2
  have hde : X.F.dist j x + X.L₁ + 1 ≤ X.F.dist j (X.F.oldest j x) := by
    unfold Frames.dist
    omega
  have hew : X.F.dist j (X.F.oldest j x) ≤ X.F.dist j (X.F.fr (j - 1) 0) := by
    unfold Frames.dist
    omega
  have hP : (13 : ℝ) ≤ p := by exact_mod_cast hX.p13
  have hP0 : (0 : ℝ) < p := by linarith
  have hP1 : (1 : ℝ) ≤ p := by linarith
  have hk : (5 : ℝ) ≤ Dat.k (r := r) K := b.k5
  have hY := b.Y1
  have hNs := b.Ns1
  have hden := den_pos hX j
  have hTa : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j = X.a := by
    unfold Tj
    exact mul_div_cancel₀ _ hden.ne'
  have hRT := pow_Rj_le hX j
  have hRp : (0 : ℝ) ≤ (p : ℝ) ^ X.Rj p K j := by positivity
  have hTp : (0 : ℝ) ≤ Tj X p K j := hRp.trans hRT
  have ha : 0 ≤ X.a := hTa ▸ mul_nonneg hden.le hTp
  have hLd : (p : ℝ) ^ (X.L₁ + X.F.dist j x) ≤ (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) :=
    pow_le_pow_right₀ hP1 (by omega)
  have hLe : (p : ℝ) * (p : ℝ) ^ (X.L₁ + X.F.dist j x) ≤ (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hP1 (by omega)
  have hLpos : (0 : ℝ) < (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by positivity
  have hEpos : (0 : ℝ) < (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by positivity
  have hA : Dat.k (r := r) K * (p : ℝ) ^ X.Rj p K j ≤ X.a / (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by
    rw [le_div_iff₀ hLpos]
    have h8 : 1 ≤ 8 * X.Y * Dat.k (r := r) K * (X.Ns : ℝ) := by
      have : (1 : ℝ) ≤ X.Y * Dat.k (r := r) K := by nlinarith
      have : (1 : ℝ) ≤ X.Y * Dat.k (r := r) K * (X.Ns : ℝ) := by nlinarith
      linarith
    have hq : 0 ≤ Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by positivity
    calc Dat.k (r := r) K * (p : ℝ) ^ X.Rj p K j * (p : ℝ) ^ (X.L₁ + X.F.dist j x)
        ≤ Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hRT (by linarith)) hLd hLpos.le (by positivity)
      _ ≤ (8 * X.Y * Dat.k (r := r) K * (X.Ns : ℝ)) * (Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0)) := le_mul_of_one_le_left hq h8
      _ = X.a := by rw [← hTa]; ring
  have hB : (p : ℝ) ^ X.Rj p K j * (4 * X.a * ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x) + X.Rj p K j))⁻¹) ≤ X.a / (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by
    rw [pow_add, mul_inv, le_div_iff₀ hLpos]
    have hRpos : (0 : ℝ) < (p : ℝ) ^ X.Rj p K j := by positivity
    have e : (p : ℝ) ^ X.Rj p K j * (4 * X.a * (((p : ℝ) ^ X.F.dist j (X.F.oldest j x))⁻¹ * ((p : ℝ) ^ X.Rj p K j)⁻¹)) = 4 * X.a / (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by
      field_simp
    rw [e, div_mul_eq_mul_div, div_le_iff₀ hEpos]
    nlinarith [mul_le_mul_of_nonneg_left hLe ha, mul_nonneg (mul_nonneg ha hLpos.le) (by linarith : (0 : ℝ) ≤ p - 4)]
  have z1 : (p : ℝ) ^ (-((X.F.dist j (X.F.oldest j x) : ℤ) + (X.Rj p K j : ℤ))) = ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x) + X.Rj p K j))⁻¹ := by
    rw [← Nat.cast_add, zpow_neg, zpow_natCast]
  have z2 : (p : ℝ) ^ (-((X.L₁ : ℤ) + (X.F.dist j x : ℤ))) = ((p : ℝ) ^ (X.L₁ + X.F.dist j x))⁻¹ := by
    rw [← Nat.cast_add, zpow_neg, zpow_natCast]
  have hkne : Dat.k (r := r) K ≠ 0 := by linarith
  have hT1 : (p : ℝ) ^ X.Rj p K j * (X.La * X.a / ((p : ℝ) * Dat.k (r := r) K * (p : ℝ) ^ (X.F.dist j x + X.Rj p K j))) = X.La * X.a / ((p : ℝ) * Dat.k (r := r) K * (p : ℝ) ^ X.F.dist j x) := by
    rw [pow_add]
    field_simp
  rw [div_eq_mul_inv] at hA hB
  have hI : 0 ≤ X.a * ((p : ℝ) ^ (X.L₁ + X.F.dist j x))⁻¹ := mul_nonneg ha (inv_nonneg.mpr hLpos.le)
  unfold Dat.oc Dat.o
  push_cast
  rw [z1, z2, mul_add, hT1]
  split_ifs <;> linarith

end Formalism.MainNotions.SelectionLemmas.Pf

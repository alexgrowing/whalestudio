import Mathlib

noncomputable section

namespace PI.OmVe

theorem prodSplit_closed (x : ℝ) (hx : x ≠ 0) (M : ℕ) : ∀ a, a ≤ M →
    ∏ i : Fin a, (x ^ M - x ^ (i : ℕ)) = x ^ (M * a) * ∏ j ∈ Finset.Icc (M - a + 1) M, (1 - x ^ (-(j : ℤ))) := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), show a + 1 + m - a + 1 = m + 1 + 1 by omega,
      show a + 1 + m - (a + 1) + 1 = m + 1 by omega,
      ← Finset.insert_Icc_add_one_left_eq_Icc (by omega : m + 1 ≤ a + 1 + m), Finset.prod_insert (by simp),
      mul_add_one, zpow_neg, zpow_natCast]
    have hpow : x ^ (a + 1 + m) = x ^ a * x ^ (m + 1) := by
      rw [← pow_add]
      ring_nf
    rw [pow_add x ((a + 1 + m) * a) (a + 1 + m), hpow]
    have hw : x ^ (m + 1) ≠ 0 := pow_ne_zero _ hx
    field_simp

theorem prodInert_closed (x : ℝ) (hx : x ≠ 0) (M : ℕ) : ∀ a, a ≤ M →
    ∏ j : Fin a, (x ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * x ^ (M - j - 1)) =
      x ^ (2 * M * a - a ^ 2) * ∏ j ∈ Finset.Icc (M - a + 1) M, (1 - (-1) ^ j * x ^ (-(j : ℤ))) := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), show a + 1 + m - a + 1 = m + 1 + 1 by omega,
      show a + 1 + m - (a + 1) + 1 = m + 1 by omega,
      ← Finset.insert_Icc_add_one_left_eq_Icc (by omega : m + 1 ≤ a + 1 + m), Finset.prod_insert (by simp),
      zpow_neg, zpow_natCast, show a + 1 + m - a = m + 1 by omega,
      show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show m + 1 - 1 = m by omega]
    have h1 : 2 * (a + 1 + m) * a - a ^ 2 = a ^ 2 + 2 * a + 2 * a * m := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    have h2 : 2 * (a + 1 + m) * (a + 1) - (a + 1) ^ 2 = a ^ 2 + 2 * a + 2 * a * m + (2 * m + 1) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    rw [h1, h2, pow_add]
    have hw : x ^ (m + 1) ≠ 0 := pow_ne_zero _ hx
    field_simp
    ring

end PI.OmVe

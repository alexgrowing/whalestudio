import Mathlib

open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Ra

theorem carry : ∀ (p f : ℕ), 2 ≤ p → 0 < f → ∀ (y : ℕ → NNReal), (∀ n, y (n + f) = y n) → (∀ n, y n ≤ 1) → (∀ n, y n ^ p ≤ y (n + 1)) → ∀ (e : Fin f → ℕ) (j : ℕ), 2 ≤ ∑ n, e n → (∑ n : Fin f, e n * p ^ (n : ℕ)) ≡ p ^ (j + 1) [MOD (p ^ f - 1)] → ∏ n : Fin f, y n ^ e n ≤ y j ^ p := by
  intro p f hp hf y hper hle1 hstep e j he hcong
  have hperm : ∀ a c, y (a + f * c) = y a := by
    intro a c
    induction c with
    | zero => simp
    | succ c ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  have hiter : ∀ a k, y a ^ (p ^ k) ≤ y (a + k) := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ← Nat.add_assoc]
      exact (pow_le_pow_left₀ zero_le ih p).trans (hstep _)
  obtain ⟨q, s, hs, hj⟩ : ∃ q s, s < f ∧ j = s + f * q :=
    ⟨j / f, j % f, Nat.mod_lt _ hf, (Nat.mod_add_div j f).symm⟩
  have hk : ∀ n : Fin f, ∃ k c m c', k + m = f - 1 ∧ (n : ℕ) + k = s + f * c ∧
      m + (j + 1) = n + f * c' := by
    intro n
    have hn := n.isLt
    by_cases h : (n : ℕ) ≤ s
    · refine ⟨s - n, 0, f - 1 - (s - n), q + 1, by omega, by omega, ?_⟩
      rw [hj, Nat.mul_succ]
      omega
    · refine ⟨s + f - n, 1, f - 1 - (s + f - n), q, by omega, by omega, ?_⟩
      rw [hj]
      omega
  choose k c m c' hkm hkc hmc using hk
  have hyk : ∀ n : Fin f, y n ^ (p ^ k n) ≤ y j := by
    intro n
    have := hiter n (k n)
    rw [hkc, hperm] at this
    rw [hj, hperm]
    exact this
  have hpos : 1 ≤ p := by omega
  have hN : p ^ f - 1 + 1 = p ^ f := Nat.sub_add_cancel (Nat.one_le_pow _ _ hpos)
  have hT1 : (∑ n : Fin f, e n * p ^ m n) ≡ 1 [MOD (p ^ f - 1)] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have hc := (ZMod.natCast_eq_natCast_iff _ _ _).2 hcong
    push_cast at hc ⊢
    set u : ZMod (p ^ f - 1) := (p : ZMod (p ^ f - 1)) with hu
    have huf : u ^ f = 1 := by
      rw [hu, ← Nat.cast_pow, ← hN, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    have hper' : ∀ a c, u ^ (a + f * c) = u ^ a := by
      intro a c
      rw [pow_add, pow_mul, huf, one_pow, mul_one]
    have hunit : IsUnit (u ^ (j + 1)) := by
      refine IsUnit.pow _ (isUnit_iff_exists_inv.2 ⟨u ^ (f - 1), ?_⟩)
      rw [← pow_succ', Nat.sub_add_cancel hf, huf]
    have hmul : (∑ n : Fin f, (e n : ZMod (p ^ f - 1)) * u ^ m n) * u ^ (j + 1) = u ^ (j + 1) := by
      refine (Finset.sum_mul _ _ _).trans ((Finset.sum_congr rfl fun n _ => ?_).trans hc)
      rw [mul_assoc, ← pow_add, hmc, hper']
    have h0 : ((∑ n : Fin f, (e n : ZMod (p ^ f - 1)) * u ^ m n) - 1) * u ^ (j + 1) = 0 := by
      rw [sub_mul, hmul, one_mul, sub_self]
    exact sub_eq_zero.1 (hunit.mul_left_eq_zero.1 h0)
  have hT2 : 2 ≤ ∑ n : Fin f, e n * p ^ m n :=
    le_trans he (Finset.sum_le_sum fun n _ => Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  have hTf : p ^ f ≤ ∑ n : Fin f, e n * p ^ m n := by
    have hd := (Nat.modEq_iff_dvd' (by omega : 1 ≤ ∑ n : Fin f, e n * p ^ m n)).1 hT1.symm
    have hle := Nat.le_of_dvd (by omega) hd
    generalize p ^ f = P at *
    generalize ∑ n : Fin f, e n * p ^ m n = T at *
    omega
  have hP : 0 < p ^ (f - 1) := pow_pos (by omega) _
  refine (pow_le_pow_iff_left₀ zero_le zero_le hP.ne').1 ?_
  calc (∏ n : Fin f, y n ^ e n) ^ p ^ (f - 1)
      = ∏ n : Fin f, (y n ^ p ^ k n) ^ (e n * p ^ m n) := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun n _ => ?_
        rw [← pow_mul, ← pow_mul]
        congr 1
        rw [← hkm n, pow_add]
        ring
    _ ≤ ∏ n : Fin f, y j ^ (e n * p ^ m n) :=
        Finset.prod_le_prod (fun _ _ => zero_le) fun n _ => pow_le_pow_left₀ zero_le (hyk n) _
    _ = y j ^ (∑ n : Fin f, e n * p ^ m n) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ y j ^ p ^ f := pow_le_pow_of_le_one zero_le (hle1 j) hTf
    _ = (y j ^ p) ^ p ^ (f - 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 2
        omega

end PositivityTheory.HtPt.Ra

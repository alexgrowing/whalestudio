import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree

namespace GlobalTheory.EX

theorem lt_of_prime_mod_eq_one {p M : ℕ} (hp : p.Prime) (h : p % M = 1) (hM : 0 < M) : M < p := by
  by_contra hc
  rcases (not_lt.mp hc).lt_or_eq with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt] at h
    exact hp.one_lt.ne' h
  · subst heq
    simp at h

theorem mod_eq_one_of_mod_mul {p M K : ℕ} (h : p % (M * K) = 1) (hM : 1 < M) : p % M = 1 := by
  rw [← Nat.mod_mul_right_mod p M K, h, Nat.mod_eq_of_lt hM]

theorem auxiliary_primes : SmallPrimeOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N → ∃ p p' q0 : ℕ, p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧ p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 := by
  rintro ⟨A, hA, hS⟩
  have hA0 : 0 ≤ A := by linarith
  refine ⟨(2 + 2 * A + (2 + 2 * A) * A) * A, by nlinarith [mul_nonneg hA0 hA0, mul_nonneg hA0 (mul_nonneg hA0 hA0)], ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have key : ∀ (M : ℕ) (e : ℝ), 2 ≤ M → (M : ℝ) ≤ (N : ℝ) ^ e →
      ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ (e * A) := by
    intro M e hM hMe
    obtain ⟨p, hp, hpm, hple⟩ := hS M hM
    refine ⟨p, hp, hpm, hple.trans ?_⟩
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hMe hA0
  have h15 : ((15 * N : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have : (30 : ℝ) ≤ N := by exact_mod_cast hN
    rw [Real.rpow_two]; push_cast; nlinarith
  have hM1 : 2 ≤ 15 * N := by omega
  obtain ⟨p, hp, hpm, hple⟩ := key (15 * N) 2 hM1 h15
  have hM2 : 2 ≤ 15 * N * p := hM1.trans (Nat.le_mul_of_pos_right _ hp.pos)
  have hb2 : ((15 * N * p : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 + 2 * A) := by
    rw [Real.rpow_add hN0, Nat.cast_mul (15 * N) p]
    exact mul_le_mul h15 hple (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)
  obtain ⟨p', hp', hpm', hple'⟩ := key (15 * N * p) _ hM2 hb2
  have hM3 : 2 ≤ 15 * N * p * p' := hM2.trans (Nat.le_mul_of_pos_right _ hp'.pos)
  have hb3 : ((15 * N * p * p' : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 + 2 * A + (2 + 2 * A) * A) := by
    rw [Real.rpow_add hN0, Nat.cast_mul (15 * N * p) p']
    exact mul_le_mul hb2 hple' (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)
  obtain ⟨q, hq, hqm, hqle⟩ := key (15 * N * p * p') _ hM3 hb3
  have l1 : 15 * N * p < p' := lt_of_prime_mod_eq_one hp' hpm' (by omega)
  have l2 : 15 * N * p * p' < q := lt_of_prime_mod_eq_one hq hqm (by omega)
  have l3 : p ≤ 15 * N * p := Nat.le_mul_of_pos_left _ (by omega)
  have l4 : p' ≤ 15 * N * p * p' := Nat.le_mul_of_pos_left _ (by omega)
  have hAA := mul_nonneg hA0 hA0
  have hAAA := mul_nonneg hA0 hAA
  refine ⟨p, p', q, hp, hp', hq, by omega, by omega, by omega, hpm,
    mod_eq_one_of_mod_mul hpm' (by omega), ?_, ?_, ?_, hqle⟩
  · have : 15 * N * p * p' = N * (15 * p * p') := by ring
    rw [this] at hqm
    exact mod_eq_one_of_mod_mul hqm (by omega)
  · exact hple.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith))
  · exact hple'.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith))

end GlobalTheory.EX

import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple.QBinomial

open GlobalTheory.JacobiTriple

theorem qPoch_succ (t : ℂ) (n : ℕ) : qPoch t (n + 1) = qPoch t n * (1 - t ^ (n + 1)) := by
  unfold qPoch; rw [Finset.prod_range_succ]

theorem qBinom_zero_right (t : ℂ) (ht : ‖t‖ < 1) (m : ℕ) : qBinom t m 0 = 1 := by
  have h := (qPoch_tendsto t ht).2.2 m
  unfold qBinom; rw [show qPoch t 0 = 1 by simp [qPoch], Nat.sub_zero]; field_simp

theorem qBinom_self (t : ℂ) (ht : ‖t‖ < 1) (m : ℕ) : qBinom t m m = 1 := by
  have h := (qPoch_tendsto t ht).2.2 m
  unfold qBinom; simp [Nat.sub_self]; rw [show qPoch t 0 = 1 by simp [qPoch]]; field_simp

theorem qBinom_pascal (t : ℂ) (ht : ‖t‖ < 1) (m k : ℕ) (hk : k < m) :
    qBinom t (m + 1) (k + 1) = qBinom t m (k + 1) + t ^ (m - k) * qBinom t m k := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - (k + 1), by omega⟩
  have hne := (qPoch_tendsto t ht).2.2
  have e1 : k + 1 + j + 1 - (k + 1) = j + 1 := by omega
  have e2 : k + 1 + j - (k + 1) = j := by omega
  have e3 : k + 1 + j - k = j + 1 := by omega
  unfold qBinom
  rw [e1, e2, e3, qPoch_succ t (k + 1 + j), qPoch_succ t k, qPoch_succ t j]
  have hk1 : (1 - t ^ (k + 1)) ≠ 0 := by
    have := hne (k + 1); rw [qPoch_succ] at this; exact right_ne_zero_of_mul this
  have hj1 : (1 - t ^ (j + 1)) ≠ 0 := by
    have := hne (j + 1); rw [qPoch_succ] at this; exact right_ne_zero_of_mul this
  have hk0 := hne k
  have hj0 := hne j
  field_simp
  ring

theorem exp_eq (m k : ℕ) (hk : k < m) : k * (k - 1) + 2 * m = (k + 1) * k + 2 * (m - k) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - (k + 1), by omega⟩
  rw [show k + 1 + j - k = j + 1 by omega]
  rcases k with _ | k
  · ring
  · simp only [Nat.add_sub_cancel]; ring

theorem qBinomial_finite : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by
  intro s X hs m
  have ht : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  induction m with
  | zero => simp [qBinom_zero_right _ ht]
  | succ m ih =>
    set f : ℕ → ℕ → ℂ := fun m k => qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k with hf
    change ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), f m k at ih
    change _ = ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k
    rw [Finset.prod_range_succ, ih, mul_add, mul_one]
    have A : ∑ k ∈ Finset.range (m + 1), f m k = f m 0 + ∑ k ∈ Finset.range m, f m (k + 1) := by
      rw [Finset.sum_range_succ', add_comm]
    have B : (∑ k ∈ Finset.range (m + 1), f m k) * (X * s ^ (2 * m)) =
        ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m)) + f m m * (X * s ^ (2 * m)) := by
      rw [Finset.sum_mul, Finset.sum_range_succ]
    have C : ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k =
        f (m + 1) 0 + ∑ k ∈ Finset.range m, f (m + 1) (k + 1) + f (m + 1) (m + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ', add_comm (f (m + 1) 0)]
    have hsum : ∑ k ∈ Finset.range m, f (m + 1) (k + 1)
        = ∑ k ∈ Finset.range m, f m (k + 1) + ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' := Finset.mem_range.mp hk
      simp only [hf]
      rw [qBinom_pascal _ ht m k hk']
      have : s ^ (k * (k - 1)) * s ^ (2 * m) = s ^ ((k + 1) * k) * (s ^ 2) ^ (m - k) := by
        rw [← pow_add, ← pow_mul, ← pow_add, exp_eq m k hk']
      simp only [Nat.add_sub_cancel]
      linear_combination (-(qBinom (s ^ 2) m k * X ^ (k + 1))) * this
    have hlast : s ^ ((m + 1) * (m + 1 - 1)) = s ^ (m * (m - 1)) * s ^ (2 * m) := by
      rw [← pow_add]; congr 1; rcases m with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]; ring
    have e0 : f (m + 1) 0 = f m 0 := by
      simp only [hf, qBinom_zero_right _ ht]
    have em : f (m + 1) (m + 1) = f m m * (X * s ^ (2 * m)) := by
      simp only [hf, qBinom_self _ ht, hlast]; ring
    rw [B, A, C, hsum, e0, em]
    ring

end GlobalTheory.JacobiTriple.QBinomial

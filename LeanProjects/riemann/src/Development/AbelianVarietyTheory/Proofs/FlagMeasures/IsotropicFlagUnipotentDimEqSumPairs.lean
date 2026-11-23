import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubledFlagSumEqUnipotentDimAndLayerProd

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadicalDimSum

theorem two_mul_pairs_add_sq {ι : Type} [LinearOrder ι] (s : Finset ι) (f : ι → ℕ) :
    2 * (∑ i ∈ s, ∑ k ∈ s.filter (fun k => i < k), f i * f k) + ∑ i ∈ s, f i ^ 2 = (∑ i ∈ s, f i) ^ 2 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    have h2 : (insert a s).filter (fun k => a < k) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact lt_irrefl _
      · exact not_lt.mpr (ha x hx).le
    have h3 : ∑ i ∈ s, ∑ k ∈ (insert a s).filter (fun k => i < k), f i * f k
        = ∑ i ∈ s, ∑ k ∈ s.filter (fun k => i < k), f i * f k + (∑ i ∈ s, f i) * f a := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.filter_insert, if_pos (ha i hi), Finset.sum_insert (by simp [hna])]
      ring
    simp only [Finset.sum_insert hna]
    rw [h2, Finset.sum_empty, h3,
      show (f a + ∑ i ∈ s, f i) ^ 2 = f a ^ 2 + 2 * (∑ i ∈ s, f i) * f a + (∑ i ∈ s, f i) ^ 2 by ring,
      ← ih]
    ring

theorem sum_shift_eq (N : ℕ) (r : ℕ → ℕ) (hr : ∀ b, N ≤ b → r b = 0) (b : ℕ) :
    ∑ c ∈ range N, r (b + c + 1) = ∑ k ∈ (range N).filter (fun k => b < k), r k := by
  have e : ∑ c ∈ range N, r (b + c + 1) = ∑ k ∈ Ico (b + 1) (b + 1 + N), r k := by
    rw [Finset.sum_Ico_eq_sum_range, show b + 1 + N - (b + 1) = N by omega]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    congr 1
    omega
  rw [e]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_Ico]
    omega
  · intro k hk hk'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_and, not_lt] at hk hk'
    apply hr
    by_contra h
    exact absurd (hk' (by omega)) (by omega)

theorem dimN_eq_sum_pairs : ∀ (n a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → dimN n j = ∑ c ∈ Finset.range (2 * a + 1), ∑ b ∈ Finset.range (2 * a + 1), r b * r (b + c + 1) := by
  intro n a j r hj ha hz
  have hpairs : ∑ c ∈ range (2 * a + 1), ∑ b ∈ range (2 * a + 1), r b * r (b + c + 1)
      = ∑ b ∈ range (2 * a + 1), ∑ k ∈ (range (2 * a + 1)).filter (fun k => b < k), r b * r k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_shift_eq (2 * a + 1) r hz b]
  have hsum : ∑ b ∈ range (2 * a + 1), r b = 2 * ∑ i, j i + (n - 2 * ∑ i, j i) := by
    have h : ∑ b ∈ range (2 * a + 1), r b = ∑ i : Fin a, (r i + r (2 * a - i)) + r a :=
      GlobalTheory.DoubledFlag.sum_range_double a r
    rw [h, ha]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hj i).1, (hj i).2]
    ring
  have hsq : ∑ b ∈ range (2 * a + 1), r b ^ 2 = 2 * ∑ i, j i ^ 2 + (n - 2 * ∑ i, j i) ^ 2 := by
    have h : ∑ b ∈ range (2 * a + 1), r b ^ 2 = ∑ i : Fin a, (r i ^ 2 + r (2 * a - i) ^ 2) + r a ^ 2 :=
      GlobalTheory.DoubledFlag.sum_range_double a (fun b => r b ^ 2)
    rw [h, ha]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hj i).1, (hj i).2]
    ring
  have h1 := two_mul_pairs_add_sq (range (2 * a + 1)) r
  have h2 := two_mul_pairs_add_sq (univ : Finset (Fin a)) j
  rw [hsum, hsq] at h1
  rw [hpairs, GlobalTheory.FlagMeas.dimN]
  nlinarith [h1, h2]

end GlobalTheory.RadicalDimSum

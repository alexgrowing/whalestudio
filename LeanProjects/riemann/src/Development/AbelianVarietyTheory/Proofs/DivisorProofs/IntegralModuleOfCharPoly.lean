import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMemStatement
open Matrix GlobalTheory.TorFin

theorem GlobalTheory.isIntMod_of_monic_dvd_affine : ∀ (A : Type) [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H : A),
    (∀ i ∈ I, H * i ∈ I) → ∀ (N : ℕ) (c q : ℕ → A), c N = 1 → (∀ k ≤ N, c k ∈ Z) →
    (∀ u : ℂ, ∑ k ∈ Finset.range (N + 1), u ^ k • c k - (u • (1 : A) + H) * ∑ k ∈ Finset.range N, u ^ k • q k ∈ I) →
    IsIntMod Z I H := by
  intro A _ _ Z I H hH N c q hcN hcZ hI
  classical
  let q' : ℕ → A := fun k => if k < N then q k else 0
  let e : ℕ → A := fun k => (if k = 0 then 0 else q' (k - 1)) + H * q' k
  have hE : ∀ u : ℂ, ∑ k ∈ Finset.range (N + 1), u ^ k • e k =
      (u • (1 : A) + H) * ∑ k ∈ Finset.range N, u ^ k • q k := by
    intro u
    have h1 : ∑ k ∈ Finset.range (N + 1), u ^ k • (if k = 0 then 0 else q' (k - 1)) =
        ∑ k ∈ Finset.range N, u ^ (k + 1) • q k := by
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, smul_zero, add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      exact Finset.sum_congr rfl fun k hk => by simp [q', Finset.mem_range.1 hk]
    have h2 : ∑ k ∈ Finset.range (N + 1), u ^ k • (H * q' k) = ∑ k ∈ Finset.range N, u ^ k • (H * q k) := by
      rw [Finset.sum_range_succ]
      simp only [q', lt_irrefl, if_false, mul_zero, smul_zero, add_zero]
      exact Finset.sum_congr rfl fun k hk => by simp [Finset.mem_range.1 hk]
    simp only [e, smul_add, Finset.sum_add_distrib]
    rw [h1, h2, add_mul, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by rw [smul_mul_assoc, one_mul, smul_smul, pow_succ']
    · exact Finset.sum_congr rfl fun k _ => (mul_smul_comm _ _ _).symm
  have hT : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * e k = 0 := by
    have h1 : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * (if k = 0 then 0 else q' (k - 1)) =
        ∑ k ∈ Finset.range N, (-H) ^ (k + 1) * q k := by
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, mul_zero, add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      exact Finset.sum_congr rfl fun k hk => by simp [q', Finset.mem_range.1 hk]
    have h2 : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * (H * q' k) = ∑ k ∈ Finset.range N, (-H) ^ k * (H * q k) := by
      rw [Finset.sum_range_succ]
      simp only [q', lt_irrefl, if_false, mul_zero, add_zero]
      exact Finset.sum_congr rfl fun k hk => by simp [Finset.mem_range.1 hk]
    simp only [e, mul_add, Finset.sum_add_distrib]
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [pow_succ, mul_assoc, ← mul_add, neg_mul, neg_add_cancel, mul_zero]
  have hd : ∀ k < N + 1, c k - e k ∈ I := GlobalTheory.T.coeff_mem_submodule_of_complex_poly_values_mem A I (N + 1) (fun k => c k - e k) fun u => by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [hE]
    exact hI u
  have hpow : ∀ k, ∀ i ∈ I, (-H) ^ k * i ∈ I := by
    intro k
    induction k with
    | zero => intro i hi; simpa using hi
    | succ k ih => intro i hi; rw [pow_succ', mul_assoc, neg_mul]; exact I.neg_mem (hH _ (ih i hi))
  have hcI : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * c k ∈ I := by
    have : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * c k = ∑ k ∈ Finset.range (N + 1), (-H) ^ k * (c k - e k) := by
      simp only [mul_sub, Finset.sum_sub_distrib, hT, sub_zero]
    rw [this]
    exact I.sum_mem fun k hk => hpow k _ (hd k (Finset.mem_range.1 hk))
  refine ⟨N, ?_⟩
  set S := Submodule.span ℂ {a | ∃ k < N, ∃ z ∈ Z, a = H ^ k * z} with hS
  have hterm : ∀ k < N, (-H) ^ k * c k ∈ S := by
    intro k hk
    have hm : H ^ k * c k ∈ S := Submodule.subset_span ⟨k, hk, c k, hcZ k hk.le, rfl⟩
    rw [neg_pow]
    rcases neg_one_pow_eq_or A k with h | h <;> rw [h]
    · simpa using hm
    · rw [neg_one_mul, neg_mul]; exact S.neg_mem hm
  have hN : (-H) ^ N ∈ I ⊔ S := by
    have : (-H) ^ N = ∑ k ∈ Finset.range (N + 1), (-H) ^ k * c k - ∑ k ∈ Finset.range N, (-H) ^ k * c k := by
      rw [Finset.sum_range_succ, hcN, mul_one, add_sub_cancel_left]
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hcI)
      (Submodule.mem_sup_right (S.sum_mem fun k hk => hterm k (Finset.mem_range.1 hk)))
  rw [neg_pow] at hN
  rcases neg_one_pow_eq_or A N with h | h <;> rw [h] at hN
  · simpa using hN
  · rw [neg_one_mul] at hN; simpa using (I ⊔ S).neg_mem hN

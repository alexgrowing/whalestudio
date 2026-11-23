import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.HtProd

theorem prod_shift_eq (N : ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀ b b', N ≤ b' → F b b' = 1) :
    ∏ c ∈ Finset.range N, ∏ b ∈ Finset.range N, F b (b + c + 1) =
      ∏ b ∈ Finset.range N, ∏ b' ∈ Finset.range N, if b < b' then F b b' else 1 := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← Finset.prod_filter]
  have h1 : ∏ c ∈ Finset.range N, F b (b + c + 1) = ∏ x ∈ Finset.Ico (b + 1) (b + 1 + N), F b x := by
    rw [Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.prod_congr rfl fun c _ => ?_
    congr 1
    omega
  rw [h1]
  symm
  apply Finset.prod_subset
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx hx'
    exact hF _ _ (by omega)

theorem prod_range_split (a : ℕ) (g : ℕ → ℝ) :
    ∏ b ∈ Finset.range (2 * a + 1), g b = (∏ i : Fin a, g i) * g a * ∏ i : Fin a, g (2 * a - i) := by
  have e : 2 * a + 1 = (a + 1) + a := by omega
  rw [e, Finset.prod_range_add, Finset.prod_range_succ, Fin.prod_univ_eq_prod_range g a,
    Fin.prod_univ_eq_prod_range (fun i => g (2 * a - i)) a, ← Finset.prod_range_reflect (fun i => g (2 * a - i)) a]
  congr 1
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Finset.mem_range] at hx
  congr 1
  omega

theorem prod_symm_split {a : ℕ} (P : Fin a → Fin a → ℝ) (hP : ∀ i k, P i k = P k i) :
    ∏ i, ∏ k, P i k = (∏ i, ∏ k, if i < k then P i k else 1) ^ 2 * ∏ i, P i i := by
  have h1 : ∀ i k, P i k = (if i < k then P i k else 1) * (if k < i then P k i else 1) *
      (if i = k then P i k else 1) := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le, hP i k]
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => h1 i k]
  simp only [Finset.prod_mul_distrib]
  rw [Finset.prod_comm (f := fun i k => if k < i then P k i else 1), sq]
  simp

theorem htProd : ∀ (n f a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ) (τ : Fin a → ℝ) (h : ℕ → ℝ),
    (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i →
    (∀ b, 2 * a + 1 ≤ b → r b = 0) →
    (∀ i : Fin a, 0 < τ i ∧ h i = τ i ^ (2 * f * j i) ∧ h (2 * a - i) = (τ i ^ (2 * f * j i))⁻¹) →
    h a = 1 → (∀ b, 2 * a + 1 ≤ b → h b = 1) →
    ∏ c ∈ Finset.range (2 * a + 1), ∏ b ∈ Finset.range (2 * a + 1),
      h b ^ r (b + c + 1) / h (b + c + 1) ^ r b = layerProd n f j τ id ^ 2 := by
  intro n f a j r τ h hr hra hr0 hτ ha h1
  rw [prod_shift_eq (2 * a + 1) (fun b b' => h b ^ r b' / h b' ^ r b)
    (fun b b' hb => by simp [hr0 b' hb, h1 b' hb])]
  unfold layerProd
  rw [← hra]
  simp only [prod_range_split, id]
  have c1 : ∀ i : Fin a, (i : ℕ) < a := fun i => i.2
  have c2 : ∀ i k : Fin a, (i : ℕ) < 2 * a - k := fun i k => by omega
  have c3 : ∀ k : Fin a, ¬ a < (k : ℕ) := fun k => by omega
  have c4 : ∀ k : Fin a, a < 2 * a - k := fun k => by omega
  have c5 : ∀ i k : Fin a, ¬ 2 * a - i < (k : ℕ) := fun i k => by omega
  have c6 : ∀ i : Fin a, ¬ 2 * a - i < a := fun i => by omega
  have c7 : ∀ i k : Fin a, (2 * a - i < 2 * a - k) ↔ k < i := fun i k => by
    rw [Fin.lt_def]; omega
  have c8 : ∀ i k : Fin a, ((i : ℕ) < k) ↔ i < k := fun i k => Iff.rfl
  simp only [c1, c2, c3, c4, c5, c6, c7, c8, lt_irrefl, if_true, if_false, ha,
    fun i => (hr i).1, fun i => (hr i).2, fun i => (hτ i).2.1, fun i => (hτ i).2.2,
    Finset.prod_const_one, one_mul, mul_one, one_pow, div_one, Finset.prod_mul_distrib,
    Finset.prod_filter]
  have d1 : ∀ i k : Fin a, (τ i ^ (2 * f * j i)) ^ j k / (τ k ^ (2 * f * j k)) ^ j i =
      (τ i / τ k) ^ (2 * j i * j k * f) := fun i k => by
    rw [div_pow, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have d2 : ∀ i k : Fin a, (τ i ^ (2 * f * j i)) ^ j k / (τ k ^ (2 * f * j k))⁻¹ ^ j i =
      (τ i * τ k) ^ (2 * j i * j k * f) := fun i k => by
    rw [inv_pow, div_inv_eq_mul, mul_pow, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have d3 : ∀ i k : Fin a, (τ i ^ (2 * f * j i))⁻¹ ^ j k / (τ k ^ (2 * f * j k))⁻¹ ^ j i =
      (τ k / τ i) ^ (2 * j k * j i * f) := fun i k => by
    rw [← d1, inv_pow, inv_pow, div_inv_eq_mul, mul_comm, div_eq_mul_inv]
  have d4 : ∀ i : Fin a, (τ i ^ (2 * f * j i)) ^ r a = τ i ^ (2 * j i * r a * f) := fun i => by
    rw [← pow_mul]
    congr 1
    ring
  have d5 : ∀ i : Fin a, 1 / (τ i ^ (2 * f * j i))⁻¹ ^ r a = τ i ^ (2 * j i * r a * f) := fun i => by
    rw [← d4, inv_pow, one_div, inv_inv]
  have d6 : ∀ i : Fin a, (τ i * τ i) ^ (2 * j i * j i * f) = ((τ i ^ 2) ^ (j i ^ 2 * f)) ^ 2 := fun i => by
    rw [← sq, ← pow_mul (τ i ^ 2)]
    congr 1
    ring
  simp only [d1, d2, d3, d4, d5]
  rw [Finset.prod_comm (f := fun i k => if k < i then (τ k / τ i) ^ (2 * j k * j i * f) else 1),
    prod_symm_split (fun i k => (τ i * τ k) ^ (2 * j i * j k * f))
      (fun i k => by rw [mul_comm (τ i)]; congr 1; ring)]
  simp only [d6, Finset.prod_pow]
  ring

end GlobalTheory.HtProd

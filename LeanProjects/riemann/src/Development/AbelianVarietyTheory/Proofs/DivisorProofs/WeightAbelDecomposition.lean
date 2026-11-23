import Mathlib

open scoped ComplexOrder Matrix

namespace GlobalTheory

theorem abel_sum_Icc_one (lam x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, lam i * x i =
      (∑ i ∈ Finset.Ico 1 n, (lam i - lam (i + 1)) * ∑ l ∈ Finset.Icc 1 i, x l) +
        lam n * ∑ l ∈ Finset.Icc 1 n, x l := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top hn,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1) x, ih]
    ring

theorem abel_sum_tail (lam x : ℕ → ℝ) (j N : ℕ) (h : j + 1 ≤ N) :
    ∑ i ∈ Finset.Icc (j + 1) N, lam i * x i =
      lam (j + 1) * (∑ l ∈ Finset.Icc (j + 1) N, x l) -
        ∑ i ∈ Finset.Ico (j + 1) N, (lam i - lam (i + 1)) * ∑ l ∈ Finset.Icc (i + 1) N, x l := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have h1 : ∑ i ∈ Finset.Ico (j + 1) n, (lam i - lam (i + 1)) *
          ∑ l ∈ Finset.Icc (i + 1) (n + 1), x l =
        (∑ i ∈ Finset.Ico (j + 1) n, (lam i - lam (i + 1)) * ∑ l ∈ Finset.Icc (i + 1) n, x l) +
          (∑ i ∈ Finset.Ico (j + 1) n, (lam i - lam (i + 1))) * x (n + 1) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_Ico.mp hi
      rw [Finset.sum_Icc_succ_top (by omega)]
      ring
    have h2 : ∀ m, j + 1 ≤ m →
        ∑ i ∈ Finset.Ico (j + 1) m, (lam i - lam (i + 1)) = lam (j + 1) - lam m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ m hm ihm => rw [Finset.sum_Ico_succ_top hm, ihm]; ring
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top hn,
      Finset.sum_Icc_succ_top (by omega : j + 1 ≤ n + 1) x, h1, h2 n hn, ih]
    simp only [Finset.Icc_self, Finset.sum_singleton]
    ring

theorem sum_Icc_one_split (f : ℕ → ℝ) (j N : ℕ) (h : j ≤ N) :
    ∑ i ∈ Finset.Icc 1 N, f i =
      ∑ i ∈ Finset.Icc 1 j, f i + ∑ i ∈ Finset.Icc (j + 1) N, f i := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega : j + 1 ≤ n + 1), ih]
    ring

theorem weight_abel_decomposition :
    ∀ (N j : ℕ) (lam x : ℕ → ℝ), 1 ≤ j → j < N → -(∑ i ∈ Finset.Icc 1 N, lam i * x i) = (∑ i ∈ Finset.Ico 1 j, (lam i - lam (i + 1)) * -(∑ l ∈ Finset.Icc 1 i, x l)) + (lam j - lam (j + 1)) * -(∑ l ∈ Finset.Icc 1 j, x l) + (∑ i ∈ Finset.Ioo j N, (lam i - lam (i + 1)) * ∑ l ∈ Finset.Icc (i + 1) N, x l) - lam (j + 1) * ∑ l ∈ Finset.Icc 1 N, x l := by
  intro N j lam x hj hjN
  have hI : Finset.Ioo j N = Finset.Ico (j + 1) N := by
    ext i; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
  rw [hI, sum_Icc_one_split (fun i => lam i * x i) j N hjN.le, sum_Icc_one_split x j N hjN.le,
    abel_sum_Icc_one lam x j hj, abel_sum_tail lam x j N hjN]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

end GlobalTheory

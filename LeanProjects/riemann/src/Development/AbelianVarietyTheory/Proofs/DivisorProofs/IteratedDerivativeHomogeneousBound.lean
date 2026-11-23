import Mathlib

open MvPolynomial Finset

namespace GlobalTheory

theorem iterate_pderiv_monomial_descFactorial {σ : Type*} (i : σ) (n : ℕ) (m : σ →₀ ℕ) (c : ℝ) :
    (pderiv i)^[n] (monomial m c) =
      monomial (m - Finsupp.single i n) (c * ((m i).descFactorial n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pderiv_monomial, Nat.descFactorial_succ, tsub_tsub,
      ← Finsupp.single_add]
    congr 1
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
    push_cast
    ring

theorem iterate_pderiv_finset_sum {σ ι : Type*} (i : σ) (n : ℕ) (s : Finset ι)
    (f : ι → MvPolynomial σ ℝ) :
    (pderiv i)^[n] (∑ a ∈ s, f a) = ∑ a ∈ s, (pderiv i)^[n] (f a) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_sum]

theorem abs_eval_iterate_pderiv_monomial_le {N k n : ℕ} (m : Fin N →₀ ℕ) (c : ℝ) (i : Fin N)
    (U : ℝ) (v : Fin N → ℝ) (hm : ∑ a, m a = k) (hU : 0 ≤ U) (hv : ∀ a, |v a| ≤ U) :
    |eval v ((pderiv i)^[n] (monomial m c))| ≤ |c| * (k : ℝ) ^ n * U ^ (k - n) := by
  rw [iterate_pderiv_monomial_descFactorial]
  by_cases h : m i < n
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h]
    simp only [Nat.cast_zero, mul_zero, map_zero, abs_zero, monomial_zero]
    positivity
  · push_neg at h
    have hik : m i ≤ k := hm ▸ Finset.single_le_sum (f := fun a => m a)
      (fun a _ => Nat.zero_le _) (Finset.mem_univ i)
    have hsum : ∑ a, (m - Finsupp.single i n : Fin N →₀ ℕ) a = k - n := by
      have h1 : ∑ a, ((m - Finsupp.single i n : Fin N →₀ ℕ) a + Finsupp.single i n a) = k := by
        rw [← hm]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [Finsupp.coe_tsub, Pi.sub_apply]
        by_cases ha : a = i
        · subst ha; simp only [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_eq_of_ne ha]; omega
      rw [Finset.sum_add_distrib] at h1
      have h2 : ∑ a, (Finsupp.single i n : Fin N →₀ ℕ) a = n := by
        simp [Finsupp.single_apply]
      omega
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun a => pow_zero _), abs_mul, abs_mul,
      Finset.abs_prod, ← hsum, ← Finset.prod_pow_eq_pow_sum]
    have h3 : |(((m i).descFactorial n : ℕ) : ℝ)| ≤ (k : ℝ) ^ n := by
      rw [Nat.abs_cast]
      exact_mod_cast (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left hik n)
    refine mul_le_mul (mul_le_mul_of_nonneg_left h3 (abs_nonneg _)) ?_ ?_ (by positivity)
    · refine Finset.prod_le_prod (fun a _ => abs_nonneg _) fun a _ => ?_
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hv a) _
    · exact Finset.prod_nonneg fun a _ => abs_nonneg _

theorem abs_eval_iterate_pderiv_homogeneous_le :
    ∀ (N k n : ℕ) (rr : MvPolynomial (Fin N) ℝ) (i : Fin N) (U : ℝ) (v : Fin N → ℝ),
      rr.IsHomogeneous k → n ≤ k → 0 ≤ U → (∀ a, |v a| ≤ U) →
      |eval v ((pderiv i)^[n] rr)| ≤
        (∑ m ∈ rr.support, |rr.coeff m|) * (k : ℝ) ^ n * U ^ (k - n) := by
  intro N k n rr i U v hr _ hU hv
  conv_lhs => rw [rr.as_sum]
  rw [iterate_pderiv_finset_sum, map_sum, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  refine abs_eval_iterate_pderiv_monomial_le m _ i U v ?_ hU hv
  have := hr (mem_support_iff.1 hm)
  rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp

end GlobalTheory

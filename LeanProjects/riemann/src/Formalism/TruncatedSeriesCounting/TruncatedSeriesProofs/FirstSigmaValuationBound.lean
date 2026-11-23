import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
import Formalism.WindowSums.PowerSeriesRelationList

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Finset

private lemma sum_erase_union_le (f : ℤ → ℕ) (A B : Finset ℤ) :
    (∑ j ∈ (A ∪ B).erase 0, f j) ≤ (∑ j ∈ A.erase 0, f j) + ∑ j ∈ B.erase 0, f j := by
  classical
  rw [Finset.erase_union_distrib]
  have h := Finset.sum_union_inter (s₁ := A.erase 0) (s₂ := B.erase 0) (f := f)
  first
  | omega
  | (rw [← h]; exact Nat.le_add_right _ _)

private lemma sum_Icc_padicValNat_add_factorial_eq (ℓ : ℕ) [Fact ℓ.Prime] (m L : ℕ) :
    (∑ n ∈ Finset.Icc (m + 1) (m + L), padicValNat ℓ n) + padicValNat ℓ m.factorial =
      padicValNat ℓ (m + L).factorial := by
  induction L with
  | zero =>
    simp only [add_zero]
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ L ih =>
    rw [show m + (L + 1) = m + L + 1 by omega, Finset.sum_Icc_succ_top (by omega), Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero _), ← ih]
    omega

private lemma sub_one_mul_padicValNat_factorial_le' (ℓ : ℕ) [Fact ℓ.Prime] (N : ℕ) :
    (ℓ - 1) * padicValNat ℓ N.factorial ≤ N := by
  rw [sub_one_mul_padicValNat_factorial]
  omega

private lemma padicValNat_factorial_add_le_add_log (ℓ : ℕ) [Fact ℓ.Prime] (m L : ℕ) :
    padicValNat ℓ (m + L).factorial ≤
      padicValNat ℓ m.factorial + padicValNat ℓ L.factorial + Nat.log ℓ (m + L) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial m L
  have hc : (m + L).choose L ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hlog : padicValNat ℓ ((m + L).choose L) ≤ Nat.log ℓ (m + L) := by
    rw [← Nat.factorization_def _ (Fact.out : ℓ.Prime)]
    exact Nat.factorization_choose_le_log
  rw [← h, padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),
    padicValNat.mul hc (Nat.factorial_ne_zero _)]
  omega

private lemma sum_Icc_one_padicValNat_eq_factorial (ℓ : ℕ) [Fact ℓ.Prime] (L : ℕ) :
    (∑ n ∈ Finset.Icc 1 L, padicValNat ℓ n) = padicValNat ℓ L.factorial := by
  have h := sum_Icc_padicValNat_add_factorial_eq ℓ 0 L
  simpa using h

theorem first_sigma_valuation_bound : TwoIntervalValuationSumBound := by
  intro ℓ _ h η S b a hab hbS
  have hℓ : ℓ.Prime := Fact.out
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have step1 := sum_erase_union_le (padicValInt ℓ) (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a))
    (Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b))
  have hI1 : (∑ j ∈ (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)).erase 0, padicValInt ℓ j) ≤
      padicValNat ℓ (η - 1).factorial + padicValNat ℓ (η + a).factorial := by
    have hsub : (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)).erase 0 ⊆
        Finset.Icc (1 - (η : ℤ)) (-1) ∪ Finset.Icc 1 ((η : ℤ) + a) := by
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union] at hj ⊢
      omega
    have hdisj : Disjoint (Finset.Icc (1 - (η : ℤ)) (-1)) (Finset.Icc 1 ((η : ℤ) + a)) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_Icc] at h1 h2
      omega
    have hneg : (∑ j ∈ Finset.Icc (1 - (η : ℤ)) (-1), padicValInt ℓ j) =
        ∑ n ∈ Finset.Icc 1 (η - 1), padicValNat ℓ n := by
      apply Finset.sum_nbij' (fun j : ℤ => ((-j).toNat : ℕ)) (fun n : ℕ => -(n : ℤ))
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        omega
      · intro n hn
        try dsimp only
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        rw [padicValInt]
        congr 1
        omega
    have hpos : (∑ j ∈ Finset.Icc 1 ((η : ℤ) + a), padicValInt ℓ j) =
        ∑ n ∈ Finset.Icc 1 (η + a), padicValNat ℓ n := by
      apply Finset.sum_nbij' (fun j : ℤ => (j.toNat : ℕ)) (fun n : ℕ => (n : ℤ))
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        omega
      · intro n hn
        try dsimp only
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        rw [padicValInt]
        congr 1
        omega
    calc _ ≤ ∑ j ∈ Finset.Icc (1 - (η : ℤ)) (-1) ∪ Finset.Icc 1 ((η : ℤ) + a), padicValInt ℓ j :=
          Finset.sum_le_sum_of_subset hsub
      _ = _ := by rw [Finset.sum_union hdisj, hneg, hpos, sum_Icc_one_padicValNat_eq_factorial, sum_Icc_one_padicValNat_eq_factorial]
  have hI2 : (∑ j ∈ (Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b)).erase 0, padicValInt ℓ j) ≤
      padicValNat ℓ (a + S).factorial + Nat.log ℓ (b - a - 1 + (a + S)) := by
    have heq : (∑ j ∈ Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b), padicValInt ℓ j) =
        ∑ n ∈ Finset.Icc (b - a - 1 + 1) (b - a - 1 + (a + S)), padicValNat ℓ n := by
      apply Finset.sum_nbij' (fun j : ℤ => ((-j).toNat : ℕ)) (fun n : ℕ => -(n : ℤ))
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn ⊢
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        omega
      · intro n hn
        try dsimp only
        omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        try dsimp only
        rw [padicValInt]
        congr 1
        omega
    have h1 := sum_Icc_padicValNat_add_factorial_eq ℓ (b - a - 1) (a + S)
    have h2 := padicValNat_factorial_add_le_add_log ℓ (b - a - 1) (a + S)
    calc _ ≤ ∑ j ∈ Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b), padicValInt ℓ j :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      _ = _ := heq
      _ ≤ _ := by omega
  have tot : (∑ j ∈ (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) ∪
        Finset.Icc (1 - ((b + S : ℕ) : ℤ)) ((a : ℤ) - b)).erase 0, padicValInt ℓ j) ≤
      padicValNat ℓ (η - 1).factorial + padicValNat ℓ (η + a).factorial +
        padicValNat ℓ (a + S).factorial + Nat.log ℓ (b - a - 1 + (a + S)) := by
    omega
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (show 1 < ℓ by omega)
  have hpos : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hsubℓ : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have r : ∀ N : ℕ, ((ℓ : ℝ) - 1) * (padicValNat ℓ N.factorial : ℝ) ≤ (N : ℝ) := by
    intro N
    have c := sub_one_mul_padicValNat_factorial_le' ℓ N
    have c' : ((ℓ - 1 : ℕ) : ℝ) * (padicValNat ℓ N.factorial : ℝ) ≤ (N : ℝ) := by exact_mod_cast c
    rwa [hsubℓ] at c'
  have hsum : (padicValNat ℓ (η - 1).factorial : ℝ) + (padicValNat ℓ (η + a).factorial : ℝ) +
      (padicValNat ℓ (a + S).factorial : ℝ) ≤ (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) := by
    rw [le_div_iff₀ hpos]
    have e1 := r (η - 1)
    have e2 := r (η + a)
    have e3 := r (a + S)
    have e4 : ((η - 1 : ℕ) : ℝ) ≤ (η : ℝ) := by exact_mod_cast Nat.sub_le η 1
    push_cast at e2 e3
    nlinarith [e1, e2, e3, e4]
  have hlam0 : 0 ≤ lam ℓ (h + η) := by
    unfold lam
    by_cases h0 : h + η = 0
    · rw [h0]
      simp
    · have h1 : (1 : ℝ) ≤ ((h + η : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      have h2 : (1 : ℝ) ≤ 2 * ((h + η : ℕ) : ℝ) := by linarith
      have := Real.logb_nonneg hℓR h2
      linarith
  have hk : ((Nat.log ℓ (b - a - 1 + (a + S)) : ℕ) : ℝ) ≤ lam ℓ (h + η) := by
    by_cases hN : b - a - 1 + (a + S) = 0
    · rw [hN, Nat.log_zero_right]
      simpa using hlam0
    · have hpow : ℓ ^ Nat.log ℓ (b - a - 1 + (a + S)) ≤ b - a - 1 + (a + S) :=
        Nat.pow_log_le_self ℓ hN
      have hNh : b - a - 1 + (a + S) ≤ 2 * (h + η) := by omega
      have hNpos : (0 : ℝ) < ((b - a - 1 + (a + S) : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hN
      have h1 : ((Nat.log ℓ (b - a - 1 + (a + S)) : ℕ) : ℝ) ≤
          Real.logb ℓ ((b - a - 1 + (a + S) : ℕ) : ℝ) := by
        rw [Real.le_logb_iff_rpow_le hℓR hNpos, Real.rpow_natCast]
        exact_mod_cast hpow
      have h2 : Real.logb ℓ ((b - a - 1 + (a + S) : ℕ) : ℝ) ≤
          Real.logb ℓ (2 * ((h + η : ℕ) : ℝ)) := by
        apply Real.logb_le_logb_of_le hℓR hNpos
        exact_mod_cast hNh
      unfold lam
      linarith
  refine le_trans (Nat.cast_le.mpr tot) ?_
  push_cast
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

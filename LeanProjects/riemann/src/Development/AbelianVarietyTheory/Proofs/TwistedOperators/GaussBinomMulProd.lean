import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialFormula
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardSubspacesOfFinrankMulCardBases

open Module GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula

namespace GlobalTheory.GaussCount

open Module in
private lemma cast_prod_pow_sub_pow_eq_prod_pow_mul_prod (q m a : ℕ) (hq : 0 < q) (h : a ≤ m) :
    ((∏ i ∈ Finset.range a, (q ^ m - q ^ i) : ℕ) : ℤ) =
      (∏ i ∈ Finset.range a, (q : ℤ) ^ i) * ∏ i ∈ Finset.range a, ((q : ℤ) ^ (m - i) - 1) := by
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq hi')]
  have e : (q : ℤ) ^ m = (q : ℤ) ^ i * (q : ℤ) ^ (m - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  push_cast
  rw [e]
  ring

open Module in
private lemma gaussBinom_self (q n : ℕ) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n n = 1 := by
  induction n with
  | zero => exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right q 0
  | succ n ih =>
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero q n (n + 1) (by omega),
      Nat.sub_self, pow_zero, ih]
    rfl

open Module in
private lemma gaussBinom_mul_prod_pow_succ_sub_one (q n a : ℕ) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a : ℤ) * ∏ i ∈ Finset.range a, ((q : ℤ) ^ (i + 1) - 1) =
      ∏ i ∈ Finset.range a, ((q : ℤ) ^ (n - i) - 1) := by
  induction n generalizing a with
  | zero =>
    rcases a with _ | a
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right]
    · rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_succ, Finset.prod_range_succ']
      simp
  | succ n ih =>
    rcases a with _ | a
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right]
    · have h1 := ih (a + 1)
      have h2 := ih a
      rw [Finset.prod_range_succ, Finset.prod_range_succ] at h1
      have hB : (∏ i ∈ Finset.range a, ((q : ℤ) ^ (n - i) - 1)) *
          ((q : ℤ) ^ (n - a) * (q : ℤ) ^ (a + 1) - (q : ℤ) ^ (n + 1)) = 0 := by
        by_cases han : a ≤ n
        · rw [← pow_add, show n - a + (a + 1) = n + 1 by omega]
          ring
        · rw [Finset.prod_eq_zero (i := n) (Finset.mem_range.mpr (by omega)) (by simp)]
          ring
      rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ, Finset.prod_range_succ, Finset.prod_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      push_cast
      linear_combination h1 + (q : ℤ) ^ (n - a) * ((q : ℤ) ^ (a + 1) - 1) * h2 + hB

open Module in
private lemma prod_pow_succ_sub_one_eq_prod_pow_sub (q n : ℕ) :
    ∏ i ∈ Finset.range n, ((q : ℤ) ^ (i + 1) - 1) = ∏ i ∈ Finset.range n, ((q : ℤ) ^ (n - i) - 1) := by
  simpa [gaussBinom_self] using gaussBinom_mul_prod_pow_succ_sub_one q n n

open Module in
private lemma prod_pow_succ_sub_one_ne_zero {q : ℕ} (hq : 1 < q) (n : ℕ) :
    ∏ i ∈ Finset.range n, ((q : ℤ) ^ (i + 1) - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have : (1 : ℤ) < (q : ℤ) ^ (i + 1) := one_lt_pow₀ (by exact_mod_cast hq) (by omega)
  linarith

open Module in
private lemma card_submodule_finrank_eq_gaussBinom (k : Type) [Field k] [Finite k] (V : Type) [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (j : ℕ) :
    Nat.card {L : Submodule k V // finrank k L = j} =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Nat.card k) (finrank k V) j := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  by_cases hj : j ≤ finrank k V
  · have h := _root_.GlobalTheory.SubspaceNumber.card_subspaces_mul k V j hj
    have hZ := congrArg (fun x : ℕ => (x : ℤ)) h
    simp only [Nat.cast_mul] at hZ
    rw [cast_prod_pow_sub_pow_eq_prod_pow_mul_prod (Nat.card k) j j (by omega) le_rfl,
      cast_prod_pow_sub_pow_eq_prod_pow_mul_prod (Nat.card k) _ j (by omega) hj,
      ← prod_pow_succ_sub_one_eq_prod_pow_sub (Nat.card k) j,
      ← gaussBinom_mul_prod_pow_succ_sub_one (Nat.card k) (finrank k V) j] at hZ
    have hQ : ∏ i ∈ Finset.range j, ((Nat.card k : ℕ) : ℤ) ^ i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ =>
        pow_ne_zero _ (by exact_mod_cast (show Nat.card k ≠ 0 by omega))
    have hF := prod_pow_succ_sub_one_ne_zero hq j
    have key : (Nat.card {L : Submodule k V // finrank k L = j} : ℤ) =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Nat.card k) (finrank k V) j := by
      apply mul_right_cancel₀ (mul_ne_zero hQ hF)
      linear_combination hZ
    exact_mod_cast key
  · rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero _ _ _ (by omega)]
    haveI : IsEmpty {L : Submodule k V // finrank k L = j} :=
      ⟨fun ⟨L, hL⟩ => by have := Submodule.finrank_le L; omega⟩
    exact Nat.card_of_isEmpty

open Module in

theorem _root_.GlobalTheory.GaussCount.subspaceCount : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.SubspaceCount := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.SubspaceCount
  intro k _ _ V _ _ _ j
  exact card_submodule_finrank_eq_gaussBinom k V j

open Module in
private lemma gaussBinom_mul_prod_mul_prod_sub_eq_prod (q n a : ℕ) (h : a ≤ n) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a : ℤ) * (∏ i ∈ Finset.range a, ((q : ℤ) ^ (i + 1) - 1)) *
        (∏ i ∈ Finset.range (n - a), ((q : ℤ) ^ (i + 1) - 1)) =
      ∏ i ∈ Finset.range n, ((q : ℤ) ^ (i + 1) - 1) := by
  rw [mul_assoc, ← mul_assoc (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a : ℤ), gaussBinom_mul_prod_pow_succ_sub_one, prod_pow_succ_sub_one_eq_prod_pow_sub q (n - a), prod_pow_succ_sub_one_eq_prod_pow_sub q n]
  have hsplit := Finset.prod_range_add (fun i => (q : ℤ) ^ (n - i) - 1) a (n - a)
  rw [Nat.add_sub_cancel' h] at hsplit
  rw [hsplit]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.sub_sub]

open Module in
private lemma gaussBinom_sub_eq_gaussBinom {q : ℕ} (hq : 1 < q) (n a : ℕ) (h : a ≤ n) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n (n - a) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a := by
  have h1 := gaussBinom_mul_prod_mul_prod_sub_eq_prod q n a h
  have h2 := gaussBinom_mul_prod_mul_prod_sub_eq_prod q n (n - a) (Nat.sub_le n a)
  rw [Nat.sub_sub_self h] at h2
  have hne := mul_ne_zero (prod_pow_succ_sub_one_ne_zero hq a) (prod_pow_succ_sub_one_ne_zero hq (n - a))
  have : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n (n - a) : ℤ) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a := by
    apply mul_right_cancel₀ hne
    linear_combination h2 - h1
  exact_mod_cast this

open Module in

theorem _root_.GlobalTheory.GaussCount.card_codim (k : Type) [Field k] [Finite k] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (j : ℕ) :
    Nat.card {L : Submodule k V // finrank k (V ⧸ L) = j} =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Nat.card k) (finrank k V) j := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  by_cases hj : j ≤ finrank k V
  · have e : {L : Submodule k V // finrank k (V ⧸ L) = j} ≃
        {L : Submodule k V // finrank k L = finrank k V - j} :=
      Equiv.subtypeEquivRight fun L => by
        have := L.finrank_quotient_add_finrank
        omega
    rw [Nat.card_congr e, card_submodule_finrank_eq_gaussBinom k V, gaussBinom_sub_eq_gaussBinom hq _ _ hj]
  · rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero _ _ _ (by omega)]
    haveI : IsEmpty {L : Submodule k V // finrank k (V ⧸ L) = j} :=
      ⟨fun ⟨L, hL⟩ => by have := L.finrank_quotient_add_finrank; omega⟩
    exact Nat.card_of_isEmpty

open Module in

theorem _root_.GlobalTheory.GaussCount.gauss_formula (q : ℕ) (R : Type) [CommRing R] (Y : R) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j =
      ∏ i ∈ Finset.range m, (1 - (q : R) ^ i * Y) := by
  induction m with
  | zero => simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right]
  | succ m ih =>
    have h0 : ∑ j ∈ Finset.range (m + 1 + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j =
        ∑ j ∈ Finset.range (m + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j := by
      rw [Finset.sum_range_succ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero q m (m + 1) (by omega)]
      simp
    have h2 := Finset.sum_range_succ' (fun j => (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) *
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j) (m + 1)
    have h1 : ∑ j ∈ Finset.range (m + 1), (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
        ((q ^ (m - j) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : ℕ) : R) * Y ^ (j + 1) =
        -((q : R) ^ m * Y) * ∑ j ∈ Finset.range (m + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
      have e : (q : R) ^ m = (q : R) ^ j * (q : R) ^ (m - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hjm]
      rw [Nat.triangle_succ, e]
      push_cast
      ring
    have hterm : ∀ j, (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
        (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q (m + 1) (j + 1) : R) * Y ^ (j + 1) =
        (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m (j + 1) : R) * Y ^ (j + 1) +
        (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
          ((q ^ (m - j) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : ℕ) : R) * Y ^ (j + 1) := by
      intro j
      rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ]
      push_cast
      ring
    rw [Finset.prod_range_succ, ← ih, Finset.sum_range_succ',
      Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, h1]
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right] at h2 ⊢
    linear_combination h0 - h2

end GlobalTheory.GaussCount

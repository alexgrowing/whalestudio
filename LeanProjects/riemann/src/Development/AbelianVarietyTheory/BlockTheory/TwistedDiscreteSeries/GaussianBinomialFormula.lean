import Mathlib

open Module

namespace GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula

def gaussBinom (q m : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun j => Nat.casesOn j 1 fun _ => 0)
    (fun m b j => Nat.casesOn j 1 fun j => b (j + 1) + q ^ (m - j) * b j) m

open Module in
@[simp] theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right (q m : ℕ) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m 0 = 1 := by
  cases m <;> rfl

@[simp] theorem gaussBinom_zero_succ (q j : ℕ) : gaussBinom q 0 (j + 1) = 0 := rfl

theorem gaussBinom_succ_succ (q m j : ℕ) :
    gaussBinom q (m + 1) (j + 1) = gaussBinom q m (j + 1) + q ^ (m - j) * gaussBinom q m j := rfl

open Module in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero (q : ℕ) :
    ∀ m j : ℕ, m < j → _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j = 0 := by
  intro m
  induction m with
  | zero =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rfl
  | succ m ih =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ, ih (j + 1) (by omega), ih j (by omega)]
    simp

def SubspaceCount : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (j : ℕ),
    Nat.card {L : Submodule k V // finrank k L = j} = gaussBinom (Nat.card k) (finrank k V) j

def OverspaceCount : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (r : ℕ) (U : Submodule k (Fin r → k)) (j : ℕ),
    Nat.card {L : Submodule k (Fin r → k) // U ≤ L ∧ finrank k ((Fin r → k) ⧸ L) = j} =
      gaussBinom (Nat.card k) (r - finrank k U) j

def GaussFormula : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (R : Type) [CommRing R] (Y : R) (m : ℕ),
    ∑ j ∈ Finset.range (m + 1),
        (-1 : R) ^ j * (Nat.card k : R) ^ (j * (j - 1) / 2) *
          (gaussBinom (Nat.card k) m j : R) * Y ^ j =
      ∏ i ∈ Finset.range m, (1 - (Nat.card k : R) ^ i * Y)

def Statement : Prop := SubspaceCount ∧ OverspaceCount ∧ GaussFormula

example : gaussBinom 2 2 1 = 3 ∧ gaussBinom 2 3 1 = 7 ∧ gaussBinom 2 3 2 = 7 ∧
    gaussBinom 2 4 2 = 35 ∧ gaussBinom 3 4 2 = 130 := by decide

example (Y : ℤ) : ∑ j ∈ Finset.range (3 + 1),
    (-1 : ℤ) ^ j * ((3 : ℕ) : ℤ) ^ (j * (j - 1) / 2) * (gaussBinom 3 3 j : ℤ) * Y ^ j =
      ∏ i ∈ Finset.range 3, (1 - ((3 : ℕ) : ℤ) ^ i * Y) := by
  simp [Finset.sum_range_succ, Finset.prod_range_succ, gaussBinom_succ_succ]
  ring

end GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula

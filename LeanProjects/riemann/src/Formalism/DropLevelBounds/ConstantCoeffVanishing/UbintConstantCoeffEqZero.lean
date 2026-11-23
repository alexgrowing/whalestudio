import Mathlib
import Formalism.DropLevelBounds.Statement
import Formalism.IncomingBounds.FlowDegreeBounds.ThmPExp

noncomputable section
open scoped BigOperators
open MvPowerSeries Finset

namespace Formalism.UnitaryBoundIntegral

open Formalism.IncomingBounds

section UBIntLemmas

variable {C : Type} [Field C] {σ : Type}

theorem ubint_mvExp_zero : mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  change ∑ k ∈ Finset.range (m.degree + 1), coeff m ((0 : MvPowerSeries σ C) ^ k) / (k.factorial : C) =
    coeff m 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    simp at h

theorem ubint_mvExp_sum [CharZero C] {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 0) :
    mvExp (∑ i ∈ s, f i) = ∏ i ∈ s, mvExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ubint_mvExp_zero]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, constantCoeff (f i) = 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h0 : constantCoeff (∑ i ∈ s, f i) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero hs
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      expSeriesAdd C σ (f a) _ (hf a (Finset.mem_insert_self a s)) h0, ih hs]

end UBIntLemmas

section UBIntRows

variable {C : Type} [Field C] {n0 : ℕ}

open Classical in

def ubint_rowPart (h : MvPowerSeries (PVar n0) C) (b : Fin n0) : MvPowerSeries (PVar n0) C :=
  fun m => if ∀ x ∈ m.support, rowOf x = b then coeff m h else 0

end UBIntRows

section UBIntMain

variable {C : Type} [Field C] {n0 : ℕ}

def ubint_box (n0 L y : ℕ) : Set (PVar n0 →₀ ℕ) :=
  {m | (∀ b, rowDegZ m b ≤ L * y) ∧ ∀ b, rowDegZ' m b ≤ y}

end UBIntMain

end Formalism.UnitaryBoundIntegral

import Mathlib

open Finsupp

namespace GlobalTheory

variable {X : Type*}

def tupleCoface (a b : X) {n : ℕ} (i : Fin (n + 2)) (x : Fin n → X) : Fin (n + 1) → X :=
  fun j => (Fin.cons a (Fin.snoc x b) : Fin (n + 2) → X)
    (if i ≤ j.castSucc then j.castSucc else j.succ)

@[simp] theorem tupleCoface_zero (a b : X) {n : ℕ} (x : Fin n → X) :
    tupleCoface a b 0 x = Fin.cons a x := by
  funext j
  simp only [tupleCoface, Fin.zero_le, if_true]
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp [← Fin.succ_castSucc]

@[simp] theorem tupleCoface_last (a b : X) {n : ℕ} (x : Fin n → X) :
    tupleCoface a b (Fin.last (n + 1)) x = Fin.snoc x b := by
  funext j
  simp [tupleCoface, (Fin.castSucc_lt_last j).not_ge]

variable (R : Type*) [Ring R] (N : Type*) [AddCommGroup N] [Module R N]

noncomputable def tupleDifferential (a b : X) (n : ℕ) :
    ((Fin n → X) →₀ N) →ₗ[R] ((Fin (n + 1) → X) →₀ N) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • lmapDomain N R (tupleCoface a b i)

noncomputable def tupleContraction (a : X) (n : ℕ) :
    ((Fin (n + 1) → X) →₀ N) →ₗ[R] ((Fin n → X) →₀ N) :=
  lcomapDomain (fun x => Fin.cons a x) (Fin.cons_right_injective (α := fun _ => X) a)

variable {R N}

@[simp] theorem tupleContraction_apply (a : X) (n : ℕ) (f : (Fin (n + 1) → X) →₀ N)
    (x : Fin n → X) : tupleContraction R N a n f x = f (Fin.cons a x) := rfl

end GlobalTheory

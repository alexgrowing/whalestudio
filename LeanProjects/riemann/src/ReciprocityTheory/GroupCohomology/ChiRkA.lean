import Mathlib

namespace ReciprocityTheory.Coh.EulerCharacteristicRank

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

open Function Module

def FG (a : ℕ → Type u) [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)] (N : ℕ) : Prop :=
  (∀ n, Module.Finite R (a n)) ∧ ∀ n, N < n → Subsingleton (a n)

noncomputable def cr (a : ℕ → Type u) [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)] (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (finrank R (a n) : ℤ)

section LES

variable {a b c : ℕ → Type u} [∀ n, AddCommGroup (a n)] [∀ n, Module R (a n)]
  [∀ n, AddCommGroup (b n)] [∀ n, Module R (b n)] [∀ n, AddCommGroup (c n)] [∀ n, Module R (c n)]
  (f : ∀ n, a n →ₗ[R] b n) (g : ∀ n, b n →ₗ[R] c n) (δ : ∀ n, c n →ₗ[R] a (n + 1))

end LES

def piOpt {α : Type u} (M : Option α → Type u) [∀ v, AddCommGroup (M v)] [∀ v, Module R (M v)] :
    (∀ v, M v) ≃ₗ[R] M none × ∀ a, M (some a) :=
  { Equiv.piOptionEquivProd with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

end ReciprocityTheory.Coh.EulerCharacteristicRank

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
open GlobalTheory.FunObj

namespace GlobalTheory

theorem chainTo_update_of_le {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, n ≤ j₀ → chainTo (Function.update k j₀ A) n = chainTo k n
  | 0, _ => rfl
  | n + 1, h => by
    show Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n = k n ∘ₗ chainTo k n
    rw [Function.update_of_ne (by omega : n ≠ j₀), chainTo_update_of_le k j₀ A n (by omega)]

theorem chainTo_update_succ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    chainTo (Function.update k j₀ A) (j₀ + 1) = A ∘ₗ chainTo k j₀ := by
  show Function.update k j₀ A j₀ ∘ₗ chainTo (Function.update k j₀ A) j₀ = _
  rw [Function.update_self, chainTo_update_of_le k j₀ A j₀ le_rfl]

theorem chainTo_update_add : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (A B : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (A + B)) n = chainTo (Function.update k j₀ A) n + chainTo (Function.update k j₀ B) n := by
  intro V _ _ k j₀ A B n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [chainTo_update_succ, chainTo_update_succ, chainTo_update_succ, LinearMap.add_comp]
  | succ n hn ih =>
    show Function.update k j₀ (A + B) n ∘ₗ chainTo (Function.update k j₀ (A + B)) n =
      Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n + Function.update k j₀ B n ∘ₗ chainTo (Function.update k j₀ B) n
    have hne : n ≠ j₀ := by omega
    rw [Function.update_of_ne hne, Function.update_of_ne hne, Function.update_of_ne hne, ih, LinearMap.comp_add]

example : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (A B : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (A + B)) n = chainTo (Function.update k j₀ A) n + chainTo (Function.update k j₀ B) n :=
  chainTo_update_add

end GlobalTheory

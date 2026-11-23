import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
open GlobalTheory.FunObj

namespace GlobalTheory.ChainSmul

theorem chainTo_update_of_le {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (B : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, n ≤ j₀ → chainTo (Function.update k j₀ B) n = chainTo k n
  | 0, _ => rfl
  | n + 1, h => by
    have hne : n ≠ j₀ := by omega
    show Function.update k j₀ B n ∘ₗ chainTo (Function.update k j₀ B) n = k n ∘ₗ chainTo k n
    rw [Function.update_of_ne hne, chainTo_update_of_le k j₀ B n (by omega)]

theorem chainTo_update_smul {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (c : ℂ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, j₀ < n → chainTo (Function.update k j₀ (c • A)) n = c • chainTo (Function.update k j₀ A) n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    show Function.update k j₀ (c • A) n ∘ₗ chainTo (Function.update k j₀ (c • A)) n =
      c • (Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · have hne : n ≠ j₀ := by omega
      rw [Function.update_of_ne hne, Function.update_of_ne hne, chainTo_update_smul k j₀ c A n h',
        LinearMap.comp_smul]
    · rw [Function.update_self, Function.update_self, chainTo_update_of_le k j₀ _ j₀ le_rfl,
        chainTo_update_of_le k j₀ _ j₀ le_rfl, LinearMap.smul_comp]

end GlobalTheory.ChainSmul

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermTransportModularFamiliesValuesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem transport_of_separating : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N w : ℕ) (m : S → ℕ) (f f' : ι → ℍ → ℂ) (u u' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ s, IsFam act (m s) (u s)) → (∀ i, QConj g N (f i) (f' i)) → (∀ s i, QConj g N (u s i) (u' s i)) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ i i' : ι, (∀ j, (∀ s, u s j τ₀ = u s i τ₀) → f j τ₀ = f i τ₀) → (∀ s, g (u s i τ₀ / ω₀ ^ m s) = u' s i' τ₁ / ω₁ ^ m s) → g (f i τ₀ / ω₀ ^ w) = f' i' τ₁ / ω₁ ^ w := by
  intro g ι S _ _ act N w m f f' u u' τ₀ τ₁ ω₀ ω₁ hN hact hf hu hq hqu hω h4 h6 i i' hsep hi
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_perm_transport_modular_families_values g ι (Option S) act N (fun o => o.elim w m)
    (fun o => o.elim f u) (fun o => o.elim f' u') τ₀ τ₁ ω₀ ω₁ hN hact
    (by rintro (_ | s); exacts [hf, hu s])
    (by rintro (_ | s) k; exacts [hq k, hqu s k]) h4 h6
  have hj : f (ρ.symm i') τ₀ = f i τ₀ := by
    apply hsep
    intro s
    have h1 : g (u s (ρ.symm i') τ₀ / ω₀ ^ m s) = u' s (ρ (ρ.symm i')) τ₁ / ω₁ ^ m s :=
      hρ (some s) (ρ.symm i')
    rw [Equiv.apply_symm_apply, ← hi s] at h1
    have h2 := g.injective h1
    exact (div_left_inj' (pow_ne_zero _ hω)).1 h2
  have h3 : g (f (ρ.symm i') τ₀ / ω₀ ^ w) = f' (ρ (ρ.symm i')) τ₁ / ω₁ ^ w :=
    hρ none (ρ.symm i')
  rwa [Equiv.apply_symm_apply, hj] at h3

end GlobalTheory.QFam

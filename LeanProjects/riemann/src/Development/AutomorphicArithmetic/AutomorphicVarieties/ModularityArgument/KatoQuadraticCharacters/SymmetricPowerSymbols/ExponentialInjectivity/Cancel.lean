import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.cancel :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (τ τ' : X.K ≃+* X.K) (s s' : Ω ≃ₐ[ℚ] Ω), admitted X τ s → admitted X τ' s' →
        ∀ (u v : X.K) (P Q R : Pt X m), IsPt X m u v P → IsPt X m (τ u) (τ v) Q → IsPt X m (τ' (τ u)) (τ' (τ v)) R →
          ∀ f, Mv X m τ s P Q 1 → Mv X m (τ.trans τ') (s' * s) P R f → Mv X m τ' s' Q R f := by
  intro Ω _ _ _ ε X m hm τ τ' s s' hτ hτ' u v P Q R hP hQ hR f h1 hf
  obtain ⟨-, -, -, htr, -⟩ := admB Ω ε X
  obtain ⟨g, -, hg⟩ := (mvEx Ω ε X m hm τ' s' hτ' _ _ _ hQ).1 R hR
  have hc := mvComp Ω ε X m hm τ τ' s s' hτ hτ' u v P Q R hP hQ hR 1 g h1 hg
  rw [map_one, one_pow, one_mul] at hc
  have hfg := ((mvEx Ω ε X m hm (τ.trans τ') (s' * s) (htr τ s τ' s' hτ hτ') u v P hP).2.2.2 R hR g f hc).1 hf
  exact ((mvEx Ω ε X m hm τ' s' hτ' _ _ _ hQ).2.2.2 R hR g f hg).2 hfg

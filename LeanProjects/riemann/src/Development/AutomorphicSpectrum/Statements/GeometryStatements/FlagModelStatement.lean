import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField

def FlagModelStatement : Prop :=
  ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (S : Type) [Finite S] (E : Type) [AddCommGroup E] [Module Ω E] (L : S → Lat M.ξ E) (g r : S → ℕ) (W : S → Submodule Ω E) (b₀ : ∀ σ, Fin (r σ) → E), (∀ a, ∃ l, w a l ≠ 0) → (∀ σ, (L σ).IsVB (g σ) (W σ)) → (∀ σ, LinearIndependent Ω (b₀ σ)) → (∀ σ k, b₀ σ k ∈ W σ) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ σ, (((L σ).pull M'.ξ f (AddMonoidHom.id E)).inter (Submodule.span Ω (Set.range (b₀ σ)))).IsFlagVBOn Set.univ (b₀ σ)) ∧ (∀ σ (n : ℕ) (p' : Cpt M'.ξ), ∃ Q : Submodule (regAt M'.ξ p') E, Disjoint Q (((L σ).pull M'.ξ f (AddMonoidHom.id E)).inter (flagStep Ω (b₀ σ) n) p') ∧ Q ⊔ ((L σ).pull M'.ξ f (AddMonoidHom.id E)).inter (flagStep Ω (b₀ σ) n) p' = (L σ).pull M'.ξ f (AddMonoidHom.id E) p') ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ σ (n : ℕ), ∃ (s : ℕ) (h : Fin s → E ⧸ flagStep Ω (b₀ σ) n), ((L σ).map (flagStep Ω (b₀ σ) n).mkQ).IsFrameAt h p) → NormAt M'.ξ f (RingHom.id Ω) p

end GlobalTheory.CompanionTheory.Ar

import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.UnitriangularFrameLift

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module IsDedekindDomain

def LAdj {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (B B' : S.V →ₗ[E] S.V) : Prop :=
  ∀ x y, S.hT (B x) y = S.hT x (B' y)

def LInt {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} (Λ : Submodule (𝓞 E) S.V)
    (B : S.V →ₗ[E] S.V) : Prop := ∀ l ∈ Λ, B l ∈ Λ

def IntegralAdjointUnimodular : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V),
    Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → ∀ B : S.V →ₗ[E] S.V, LInt Λ B → ∃ B' : S.V →ₗ[E] S.V, LAdj S B B' ∧ LInt Λ B'

def IntegralRetraction : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V) (X : Submodule E S.V),
    Submodule.IsLattice E Λ → ∃ P : S.V →ₗ[E] S.V, (∀ x ∈ X, P x = x) ∧ (∀ y, P y ∈ X) ∧ LInt Λ P

def IntegralTraceSurjective : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∃ θ : 𝓞 E, (θ : E) + star (θ : E) = 1

def IsotropicIntegralRetraction : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V) (X : Submodule E S.V),
    Formalism.HermitianLatticesTheory.IsCMUnram E → Submodule.IsLattice E Λ → Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → (∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) →
    ∃ P P' : S.V →ₗ[E] S.V, LAdj S P P' ∧ (∀ x ∈ X, P x = x) ∧ (∀ y, P y ∈ X) ∧ LInt Λ P ∧ LInt Λ P' ∧
      ∀ w y, S.hT (P' w) (P' y) = 0

def UnitriangularFrameIntegral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ)
    (F F' : LFlag S r T), IsFixedConv Λ g F → IsFixedConv Λ g F' → (∀ a, F'.fl.e a - F.fl.e a ∈ Xflag F a.val) →
    ∀ U : S.V →ₗ[E] S.V, (∀ a, U (F.fl.e a) = F'.fl.e a) → ∀ x ∈ Λ, x ∈ Xsp F → U x ∈ Λ

end Formalism.MainNotions.BridgeLemma

end

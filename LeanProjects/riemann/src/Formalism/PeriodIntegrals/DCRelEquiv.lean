import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

noncomputable section

open scoped Classical

namespace PI.DCRelEquiv

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

def NLamGroup : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (n m : S.V ≃ₗ[E] S.V),
    n ∈ NLam Λ F → m ∈ NLam Λ F → n * m ∈ NLam Λ F ∧ n⁻¹ ∈ NLam Λ F

def NLamConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (Λ : Submodule (𝓞 E) S.V) (F₁ F₂ : LFlag S r T) (g : S.V ≃ₗ[E] S.V),
    IsAutLam S Λ g → (∀ a, frame F₂ a = g (frame F₁ a)) →
    ∀ x : S.V ≃ₗ[E] S.V, x ∈ NLam Λ F₂ ↔ g⁻¹ * x * g ∈ NLam Λ F₁

def DCRelEquivAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T), Equivalence (DCRel Λ F (T' := T'))

def EqIffAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (P : LFlag S r T' → Prop), EqIff Λ F P

end PI.DCRelEquiv

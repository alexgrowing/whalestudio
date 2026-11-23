import Mathlib
import Formalism.PeriodIntegrals.AdelClassFin

noncomputable section

namespace PIW.AdelClassFin

open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

def StCong : Prop :=
  ∀ (I : AutInst) (U : Subgroup I.Gf), IsOpen (U : Set I.Gf) → ∃ g : ℕ, 1 ≤ g ∧ I.Kg g ⊆ (U : Set I.Gf)

def StKFin : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ T : Finset I.Gf, ∀ k ∈ I.Kset, ∃ t ∈ T, ∃ u ∈ I.Kg g, k = t * u

def StGenus : Prop :=
  ∀ I : AutInst, ∃ S : Finset I.Gf, ∀ x : I.Gf, ∃ γ ∈ GFf I, ∃ s ∈ S, ∃ k ∈ I.Kset, x = γ * s * k

def StTop : Prop := StCong → StKFin → StGenus → PI.AdelClassFin.AdelClassFin

def SelfDual {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (M : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ x : Fin n → E, x ∈ M ↔ ∀ y ∈ M, Formalism.UG.hform (starRingEnd E) J y x ∈ (algebraMap (𝓞 E) E).range

def IsImg {E : Type} [Field E] [NumberField E] {n : ℕ} (γ : GL (Fin n) E) (M₀ M : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v : Fin n → E, v ∈ M ↔ ∃ w ∈ M₀, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = v

def StH : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Formalism.UG.IsHerm (starRingEnd E) J → J.det ≠ 0 →
    ∃ T : Finset (Submodule (𝓞 E) (Fin n → E)), ∀ M : Submodule (𝓞 E) (Fin n → E), M.FG →
      Submodule.span E (M : Set (Fin n → E)) = ⊤ → SelfDual J M →
      ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧ ∃ M₀ ∈ T, IsImg γ M₀ M

def StDict : Prop :=
  ∀ I : AutInst, ∃ Λ : I.Gf → Submodule (𝓞 I.E) (Fin I.n → I.E),
    (∀ x, (Λ x).FG ∧ Submodule.span I.E ((Λ x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) = ⊤ ∧ SelfDual I.J (Λ x)) ∧
    (∀ x y, Λ x = Λ y → ∃ k ∈ I.Kset, y = x * k) ∧
    (∀ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J →
      ∃ c ∈ GFf I, I.fmat c = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) ∧
        ∀ x, IsImg γ (Λ x) (Λ (c * x)))

def StGenusOf : Prop := StDict → StH → StGenus

end PIW.AdelClassFin

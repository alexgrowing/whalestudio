import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def CentralNilGL (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (φ : Sm E a) : Prop :=
  ∀ zs : List (Module.End ℂ (Sm E a)), zs.length = N → (∀ z ∈ zs, z ∈ Zalg E a) →
    zs.foldr (fun z f => z f - χ z • f) φ = 0

variable (E a) in

def formsGL (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ))
    (N : ℕ) : Set (Sm E a) :=
  {φ | IsAutForm φ ∧ (∀ k ∈ L, finRep E a k φ = φ) ∧ (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ W) ∧
    ∃ χ ∈ X, CentralNilGL χ N φ}

def CoreFiniteGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W →
      ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (formsGL E a L W X N))

end GlobalTheory.HCF

end

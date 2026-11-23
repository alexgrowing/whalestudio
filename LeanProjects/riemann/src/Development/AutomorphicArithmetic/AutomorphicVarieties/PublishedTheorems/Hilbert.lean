import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.IsCondAt

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Published

open UpperTheory.V.Sd

def HilbertEisOne : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
    IsOfFinOrder ω → (∀ v, ω.locInf v (-1) = -1) → (∀ w, IsCondAt w ω (c w)) → (∃ w, c w ≠ 0) →
    ∃ (φ : TR.Sm F 2) (L : ℂ), IsHol 1 c ω φ ∧ HasExp φ.1 1 (fun _ => L) fun 𝔪 => ∑ᶠ 𝔯 ∈ {𝔯 | 𝔯 ∣ 𝔪}, chiI ω c 𝔯

def HilbertOne : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ ι : Qbar p ≃+* ℂ, ∃ N : ℕ,
    ∀ k : ℕ, 0 < k → (p - 1) * p ^ N ∣ k → ∃ (φ : TR.Sm F 2) (c₀ : (Af F)ˣ → ℂ) (c : Ideal (𝓞 F) → ℂ),
      IsHol k (fun _ => 0) 1 φ ∧ HasExp φ.1 k c₀ c ∧ (∀ y, ‖ι.symm (c₀ y) - 1‖ < 1) ∧ ∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (c 𝔪)‖ < 1

end UpperTheory.V.Published

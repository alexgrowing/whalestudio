import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.Sym3AutKOf

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Base

namespace UpperTheory.V.Z.Sym.Q

def PropEGad : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ (IrrOpen ρ → IsAutR ι (tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹))

def Up3 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin 3) (Qbar l)),
    IsAutR ι r → IsAutQ ι r

theorem PropEGad.eg (h : PropEGad) : PropEG := fun l _ Ω _ _ _ ι c hc N w φ θ h1 h2 h3 =>
  (h l Ω ι c hc N w φ θ h1 h2 h3).imp fun _ H k hk hp => (H k hk hp).imp fun _ hρ => hρ.1

end UpperTheory.V.Z.Sym.Q

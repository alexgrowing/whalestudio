import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

def PotOfFlag : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (m : Fin n → ℤ), (∀ i j, m i ≠ m j + 1) → ∀ v : HeightOneSpectrum (𝓞 F),
    ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A v →
      ∃ (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ) (a : ℕ), 0 < a ∧ IsFlagOn r (Dec (F := F) A) κ ∧
        ∀ i (s : ↥(Dec (F := F) A)), (s : G F Ω) ∈ Ine (F := F) A → κ i s ^ a = (cycBar F Ω l s ^ m i) ^ a) → Win.PotUnl r v

def AdWitA : Prop :=
  PureAll → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (φ θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ), 3 ≤ k → ∀ ρ, EisRep ι φ θ k ρ → IrrOpen ρ → OfForm ι k ρ →
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω], Module.finrank ℚ K = 2 →
      Win.WitA ι ((tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹).comp (galEmb ℚ K Ω)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal → Win.PotUnl ((tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹).comp (galEmb ℚ K Ω)) v

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

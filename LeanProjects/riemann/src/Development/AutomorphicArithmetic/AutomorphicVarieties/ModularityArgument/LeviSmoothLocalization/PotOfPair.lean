import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PotOfFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

def PotOfPair : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : W.HidaSetting l L Ω) (n : ℕ) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)) (a : ℤ) (P : GL (Fin n) (PadicAlgCl l)),
    Af.IsPairing s.c ρ (cycBar L Ω l ^ a) P →
    ∀ (ψ : ∀ v : W.Vl l L, Fin n → ↥(Dec (F := L) (s.A v)) →* (PadicAlgCl l)ˣ) (m : W.Vl l L → Fin n → ℤ),
    (∀ v i j, i < j → m v j + 2 ≤ m v i) → (∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (ψ v)) →
    (∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (ψ v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) →
    ∀ w : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → Win.PotUnl ρ w

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

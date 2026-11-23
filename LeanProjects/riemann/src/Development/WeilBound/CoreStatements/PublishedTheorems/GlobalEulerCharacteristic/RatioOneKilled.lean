import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN

def RatioOne (ℓ : ℕ) (P : FiniteSubfield → Prop) : Prop :=
  ∀ (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))), S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) → P K →
    ∀ (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
      (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S))
      [IsDiscreteRep M] [Finite M], (∃ r : ℕ, ∀ m : M, (ℓ ^ r) • m = 0) → gsEulerRatio S M ιr = 1

def RatioOneKilled (ℓ : ℕ) (P : FiniteSubfield → Prop) : Prop :=
  ∀ (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))), S.Finite →
    (∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) → P K →
    ∀ (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
      (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S))
      [IsDiscreteRep M] [Finite M], (∀ m : M, ℓ • m = 0) → gsEulerRatio S M ιr = 1

end PositivityTheory.Lit1.GEN

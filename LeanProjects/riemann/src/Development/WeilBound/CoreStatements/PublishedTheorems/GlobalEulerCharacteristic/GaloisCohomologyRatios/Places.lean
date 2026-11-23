import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.ModuleFiniteHomRep

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

theorem placesOver_stable : ∀ (τ : L.1 ≃ₐ[K.1] L.1), ∀ w ∈ (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))),
    τ • w ∈ (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
  fun τ _ hw => galSmul_mem_placesOver (S := S) τ hw

noncomputable def dPlaces [Finite S] (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1)) : ℤ :=
  letI := stableMulAction (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) (placesOver_stable (S := S) (K := K) (L := L))
  haveI : Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) := finite_placesOver (L := L.1) (S := S)
  d.toFun (↥(placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) → ZMod ℓ)
    (funPermRep (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1) (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))))

noncomputable def dInf (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1)) : ℤ :=
  d.toFun (InfinitePlace L.1 → ZMod ℓ) (funPermRep (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1) (InfinitePlace L.1))

end PositivityTheory.Lit1.GEN.X

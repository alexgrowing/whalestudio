import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayFieldStatement

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize

namespace GlobalTheory.FieldSize.WeberUnram

set_option autoImplicit false in
open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.FieldSize.WeberUnram.of_algHom {K M R : Type} [Field K] [NumberField K]
    [Field M] [Algebra K M] [Field R] [NumberField R]
    [Algebra K R] [IsAbelianGalois K R] (f : M →ₐ[K] R) :
    ∃ (_ : NumberField M) (_ : IsAbelianGalois K M),
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), _root_.GlobalTheory.NT.UnramIn R 𝔭 →
        _root_.GlobalTheory.NT.UnramIn M 𝔭 := by
  have hab : IsAbelianGalois K M := IsAbelianGalois.of_algHom f
  letI : Algebra M R := f.toRingHom.toAlgebra
  haveI : IsScalarTower K M R := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  haveI : FiniteDimensional K M := FiniteDimensional.left K M R
  haveI : FiniteDimensional ℚ M := Module.Finite.trans K M
  haveI nf : NumberField M := ⟨⟩
  exact ⟨nf, hab, fun 𝔭 h => _root_.GlobalTheory.RayMaximal.unramIn_of_tower (L := M) (M := R) h⟩

end GlobalTheory.FieldSize.WeberUnram

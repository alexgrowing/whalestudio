import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.HeightOneCompletion

open IsLocalRing

set_option autoImplicit false in
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.CompHt.algPadicInt _root_.GlobalTheory.CompHt.algPadicField
  _root_.GlobalTheory.CompHt.towerPadic _root_.GlobalTheory.CompHt.factPadic
  _root_.GlobalTheory.PadicComplexHost.isAdicComplete in
open IsLocalRing in

theorem _root_.GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] [CharZero A]
      (𝔭 : PrimeSpectrum A), 𝔭.asIdeal.height = 1 →
      ∃ (T : _root_.Formalism.L2.Pj.CDVR) (iT : Localization.AtPrime 𝔭.asIdeal →+* T.V),
        Function.Injective iT ∧ IsLocalHom iT := by
  intro A _ _ _ _ _ 𝔭 h
  obtain ⟨hdom, hic⟩ :=
    _root_.GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain 𝔭.asIdeal (Localization.AtPrime 𝔭.asIdeal)
  haveI := hdom
  haveI := hic
  haveI : IsNoetherianRing (Localization.AtPrime 𝔭.asIdeal) :=
    IsLocalization.isNoetherianRing 𝔭.asIdeal.primeCompl _ inferInstance
  have hdim : ringKrullDim (Localization.AtPrime 𝔭.asIdeal) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭.asIdeal (Localization.AtPrime 𝔭.asIdeal), h]
    rfl
  haveI := _root_.GlobalTheory.CdvrExt.isDVR_of_ringKrullDim_eq_one hdim
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors 𝔭.asIdeal)
  obtain ⟨O, _, _, _, j, r, hc, hj, hl, -, -, -⟩ :=
    _root_.GlobalTheory.exists_complete_discreteValuationRing_with_residues (Localization.AtPrime 𝔭.asIdeal)
      (ResidueField (Localization.AtPrime 𝔭.asIdeal)) (residue _) ∅ (ker_residue)
  haveI : CharZero (Localization.AtPrime 𝔭.asIdeal) := ⟨fun m n hmn =>
    Nat.cast_injective (R := A) (hinj (by rw [map_natCast, map_natCast]; exact hmn))⟩
  haveI : CharZero O := ⟨fun m n hmn =>
    Nat.cast_injective (R := Localization.AtPrime 𝔭.asIdeal)
      (hj (by rw [map_natCast, map_natCast]; exact hmn))⟩
  exact ⟨@_root_.Formalism.L2.Pj.CDVR.mk O _ _ _ hc _, j, hj, hl⟩

end GlobalTheory.HeightOneCompletion

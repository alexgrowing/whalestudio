import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Torsor
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdinaryPointInvariantUnderObjectMap
import Development.AutomorphicArithmetic.CommutativeAlgebra.AlgHTDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPreDataDescendsFg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedPolarisationKernelKilledOfUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecMapFieldCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjCorrespondenceTargetFiniteEtal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByIdealCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdemKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.crystallineComparison

noncomputable section

namespace GlobalTheory.ESOrdM

theorem stalk_normal_of_smooth (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0})
    (f : X ⟶ Sp R) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f (fun y => ?_) x
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  let _ : Algebra R ((Sp R).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have h : IsLocalization.AtPrime ((Sp R).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  have hle : y.asIdeal.primeCompl ≤ nonZeroDivisors R := y.asIdeal.primeCompl_le_nonZeroDivisors
  have hd : IsDomain ((Sp R).presheaf.stalk y) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  exact ⟨hd, isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory.ESOrdM

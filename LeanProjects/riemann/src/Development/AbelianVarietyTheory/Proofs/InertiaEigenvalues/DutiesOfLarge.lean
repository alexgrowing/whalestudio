import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleDistinctConstituents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneOfCoefRingTakenAtLiveLocalisationsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneTypePrimeOfCoefRingTakenAtLiveStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.CoefDuty

theorem duties_of_large : GlobalTheory.TwSys.Cheb → ∀ D : D7, Large D → SumRepresentations.Conclusion41 D → AutomorphicSideWildInertia.ResidualIrreducibleGood D → Duties D := by
  intro hC D hL h41 hRho
  obtain ⟨hO, hS, hT⟩ := hL
  exact ⟨hO, fun i r hr => GlobalTheory.abs_irreducible_distinct_constituents D h41 hS i r hr,
    GlobalTheory.T.designConditionAll_of_cheb_of_takenAll hC D hT, GlobalTheory.T.rowFiveOneTypePrime_of_coefRingTakenAtLive hC D hRho hT⟩

end GlobalTheory.CoefDuty

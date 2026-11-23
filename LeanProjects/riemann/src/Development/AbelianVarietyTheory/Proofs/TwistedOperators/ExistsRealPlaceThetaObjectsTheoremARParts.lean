import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceStdParamIsParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetrisationInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestTypePositiveAndDecays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCoverStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceFockDsUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingIntegralJointHarmonicPosStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSpaceContainsDiscreteSeriesTensorStatement

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta

namespace GlobalTheory.RealPlaceTheta

theorem exists_record_theta :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    ∃ X : ProvA, (∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam) ∧
      DiscreteSeriesBlattner X ∧ admQ5 X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X ∧ ArchimedeanRallisUpDownLine X ∧ ArchimedeanRallisFifth X := by
  intro hDS hHC

  obtain ⟨X, hX⟩ := GlobalTheory.exists_provA_of_forall_exists_hasParam fun p q T lam hl =>
    GlobalTheory.CoverDS.exists_hasParam hDS p q T lam hl
  have hH1 : admH1 X := GlobalTheory.FockDeg.degrees_and_adjoints X
  have hH2 : admH2 X := GlobalTheory.FockAlg.fock_structure X
  have hD1 : DiscreteSeriesBlattner X := GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hDS X hX
  have hQ5 : admQ5 X := GlobalTheory.Published.HarishChandraModules.admQ5_of_harishChandraModules hHC X
  have hQ6 : CoverHaarIntegration X := GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover X
  have hQ7 : admQ7 := TensorHW.highestWeight_tensor
  have hQ8 : admQ8 := GlobalTheory.InducedPBW.pbw_induced
  have hD2 : DiscreteSeriesPositivity X := GlobalTheory.SphJet.lowest_type_positive_and_decays X hD1 hQ5 hQ7 hQ8
  have hA1 : ArchimedeanRallisFirst X := GlobalTheory.T.doublingIntegral_jointHarmonic_pos X hH1 hH2 hD1 hD2 hQ5 hQ6 hQ7 hQ8
  have hA2 : ArchimedeanRallisSecond X := GlobalTheory.T.fockSpace_contains_discreteSeriesTensor X hH1 hH2 hD1 hD2 hQ5 hQ6 hQ7 hQ8 hA1
  have hA3 : ArchimedeanRallisUpDownLine X := GlobalTheory.T.theta_correspondence_fock_ds_uniqueness X hH1 hH2 hD1 hQ5 hQ7 hQ8 hA1 hA2
  have hA5 : ArchimedeanRallisFifth X := GlobalTheory.T.no_intertwiner_smaller_fock_to_discrete_series X hH1 hH2 hD1 hQ5
  exact ⟨X, hX, hD1, hQ5, hA1, hA2, hA3, hA5⟩

end GlobalTheory.RealPlaceTheta

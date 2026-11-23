import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSurjectiveOfAdjointNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLValuesNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCoefVanishesOffLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpannedBySatakeEigenElementsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCuspSpaceFiniteDimOfHarishChandraStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainFockVectorLevelLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainOccurringParamsNormHalfRankBoundStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParametersLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeParametersOfElementFromOneNonzeroValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsAdjointOfRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsNeZeroOfLValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLocalZetaNonvanishingOfRealStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainRealZetaNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsInCuspSpanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardInductionFixedMetric

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem ontoAll_of_classicalTheorems : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → UpPar D → OntoAll D := by
  intro hHCF hCRD hDSC hHCM hCW D hHF hUP
  have hLF : LevFacts D := GlobalTheory.T.thetaChain_level_properties D
  have hFD : FinDim D := GlobalTheory.T.thetaChainCuspSpaceFiniteDim_of_harishChandra hHCF D hLF
  have hMet : MetEx D := GlobalTheory.T.thetaChainInnerProductsExist_of_rapidDecay hCRD D
  have hES : EigSpan D := GlobalTheory.T.multiplicity_space_spanned_by_satake_eigen_elements hCRD D hFD hMet hLF
  have hPI : ParIndep D := GlobalTheory.T.thetaChain_heckeParameters_linearIndependent D
  have hPOV : ParOfVal D := GlobalTheory.T.hecke_parameters_of_element_from_one_nonzero_value hCRD D hMet hLF
  have hPB : ParBoundW D := GlobalTheory.T.theta_chain_occurring_params_norm_half_rank_bound hCRD D hLF
  have hLL : LevelLaw D := GlobalTheory.T.thetaLiftChain_fockVector_levelLaws D
  have hCS : CoefSupp D := GlobalTheory.T.thetaChainCoef_vanishes_off_level D
  have hArch : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D := GlobalTheory.T.archimedeanThetaCorrespondence_towers_real_data hDSC hHCM D
  have hRZ : RealZeta D := GlobalTheory.T.thetaChain_realZeta_nonvanishing hHCM D hArch
  have hZN : ZetaNe D := GlobalTheory.T.thetaChainLocalZetaNonvanishing_of_real D hMet hLF hLL hCS hRZ
  have hUN : UpNe D := GlobalTheory.T.thetaLiftUpwards_ne_zero_of_lValue D hHF hMet hLF hZN
  have hUS : UpSpan D := GlobalTheory.T.thetaLiftUpwards_in_cuspSpan hDSC hHCM hCRD hCW D hLF hLL
  have hUA : UpAdj D := GlobalTheory.T.thetaLiftUpwardsAdjoint_of_rapidDecay hCRD D
  have hSU : StepUp D := GlobalTheory.T.thetaLiftChain_adjoint_nonvanishing_step D hFD hPOV hUS hUA hUP hUN
  have hCL : ChainLW D := GlobalTheory.T.thetaChain_LValues_nonvanishing D
  have hCU : ChainUp D := chainUp_of D hMet hPB hCL hSU
  exact GlobalTheory.T.thetaLiftChain_surjective_of_adjoint_nonvanishing D hFD hMet hES hPI hCU

end GlobalTheory.ChainOnto

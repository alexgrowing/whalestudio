import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepScalarsOfRealisationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainStepAdjointScalarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTupleTwistedChainOfScalarHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurProductTypingsAgreeThetaChainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealLastStageNormalizedOfScalarHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDatumNormShrinkOfScalarHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealFormsRangeMultiplicityOfScalarHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfPartHavePartParamsFirstChainMemberStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepConstantsTupleIndepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainStepExactInnerProductStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainDatumLawsUnderLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainLevelIntegralRealZetaOfTwistedTransformLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainLValueQuotientFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFirstStageLValuesPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesIntegralPeelOfDoublingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterOfOneNonzeroValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainRealZetaNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistEulerFactorsRestoreProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStageSoftPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftsAdjointOfCuspRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpParameterOfTransferStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpLowerBlockParameterProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainThetaLiftUpSpanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpEqAdjointValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw

theorem scalars_of_given_all : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → GlobalTheory.Core.Rk.SW.HeckeFormNS D → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  intro hHCF hCRD hDSC hHCM hCW hHowe hUDG D G _ _ Pl0 T A Ks _ _ _ R F g hNG hHecke
  have soft : SoftQ D := GlobalTheory.T.twistedChain_stage_soft_properties hHCF hCRD D
  have law : LevelLawQ D := GlobalTheory.T.twistedChain_datum_laws_under_levels D
  have restore : Restore D := GlobalTheory.T.chainTwistEulerFactorsRestore_proof D
  have lfull : LFull D := GlobalTheory.T.twistedThetaChain_LValue_quotientFactorization D
  have upSpan : UpSpanQ D := GlobalTheory.T.twistedChain_thetaLiftUpSpan hDSC hHCM hCRD hCW D law
  have upAdj : UpAdjQ D := GlobalTheory.T.chainThetaLiftsAdjoint_of_cuspRapidDecay hCRD D
  have upVal : UpVal D := GlobalTheory.T.chain_theta_lift_up_eq_adjoint_value D soft upSpan upAdj
  have exact : StepExactNS D :=
    GlobalTheory.T.thetaLiftChainStep_exact_innerProduct D hHecke soft (GlobalTheory.T.chainTwistPlacesIntegralPeel_of_doubling hUDG hCRD D) (GlobalTheory.T.chainLevelIntegralRealZeta_of_twisted_transform_laws D law)
  have lam : StepLam D := GlobalTheory.T.twistedThetaChain_step_adjoint_scalar D soft (GlobalTheory.T.chainThetaLiftUp_parameter_of_transfer hCRD hHowe D) (GlobalTheory.T.chainThetaLiftUpLowerBlockParameter_proof hCRD D)
    (GlobalTheory.T.lowerBlockParameter_of_one_nonzeroValue D soft) upVal exact lfull restore
  have hX : RangeX R := GlobalTheory.T.realFormsRangeMultiplicity_of_scalarHypotheses R F g
  have chain : ∀ h : RangeX R, RChain R h := GlobalTheory.T.realTupleTwistedChain_of_scalarHypotheses R F g
  have zeta : RealZetaQ D := GlobalTheory.T.twistedChain_realZeta_nonvanishing hHCM D (GlobalTheory.T.archimedeanThetaCorrespondence_towers_real_data hDSC hHCM D)
  have unif : RUnif R hX := GlobalTheory.T.twistedChain_step_constants_tuple_indep R F g hNG zeta restore hX (chain hX)
    (GlobalTheory.T.realMeasureUniformInTuple_of_thetaLiftScalar R F g chain hX) (GlobalTheory.T.realQuotientVolumeGrowth_of_scalarHypotheses R F g chain hX) (GlobalTheory.T.realDatumNormShrink_of_scalarHypotheses R F g)
  exact GlobalTheory.T.chainStep_scalars_of_realisation R F g hNG soft (GlobalTheory.T.lowerBlockParameter_of_one_nonzeroValue D soft) (GlobalTheory.T.chain_first_stage_L_values_positive hCRD D) lfull lam hX
    (chain hX) (GlobalTheory.T.realLastStageNormalized_of_scalarHypotheses R F g hX) unif (GlobalTheory.T.rows_of_part_have_part_params_first_chain_member hCRD R F g chain hX) (GlobalTheory.T.schurProduct_typings_agree_thetaChain R F g)

end GlobalTheory.ChainTw

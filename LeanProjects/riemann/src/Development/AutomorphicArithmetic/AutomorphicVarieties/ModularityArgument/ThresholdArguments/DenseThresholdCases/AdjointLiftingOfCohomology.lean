import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.VwinOfEnd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThFinal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PmExTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ConductorAtMapInjectiveCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVFinalU

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.HV.DescentVanishingReductions
open UpperTheory.V.Lit UpperTheory.V.W
theorem adjoint_lift_of_prints (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.UnramifiedInputs :=
  have hN := hH.litN
  ⟨⟨_root_.UpperTheory.V.W.locPrints_of_litN hN, hN.coh.pt, hN.coh.gf, hN.coh.ge, hN.coh.uo, hN.coh.gw⟩, hH, _root_.UpperTheory.V.HV.Core.modU_of_printsH hH, levEx, lamEx (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN),
    b0Ex (phiAll (_root_.UpperTheory.V.W.cohP_alt hN))⟩
theorem adjoint_lifting_of_cohomology (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Th.AdjointLiftingTheorem := _root_.UpperTheory.V.Th.adjoint_lifting_of_cohomology hH (_root_.UpperTheory.V.W.cohP_alt hH.litN)
theorem pmEx_of_printsH (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.PMExAlt := _root_.UpperTheory.Gal.projectedFormsSystemPart.pm_exists_of_unramified_adjoint_lifting (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH) (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lifting_of_cohomology hH)
theorem countII_and_countIII_of_printsH_of_sp4In (hH : _root_.UpperTheory.V.Af.HypothesesH') (hK : ∃ CK : ℝ, LemmaK CK) (hS : _root_.UpperTheory.V.Aut.SymplecticFourImageDense) : CountII ∧ CountIII := by
  have hN := hH.litN
  obtain ⟨CK, hL⟩ := hK
  refine _root_.UpperTheory.V.Th.sp4Main_alt hS (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH).coh Alg.M.main_holds Alg.M.mprime_holds Alg.lemmaP (_root_.UpperTheory.GalN.V.numberSp4_n_alt hH.toClassicalTheorems)
    (_root_.UpperTheory.V.Th.rigSp4_alt (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH) (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lifting_of_cohomology hH)) (X.corX X.lemmaX X.residual_bernoulli_nonvanishing) fun Ω _ _ _ l _ => ⟨?_, fun c => ?_⟩
  · exact X.soBar CK hL (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK ℚ Ω l
  · exact X.soFin CK hL (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK ℚ Ω l c.O
end UpperTheory.V.HV.DescentVanishingReductions
end

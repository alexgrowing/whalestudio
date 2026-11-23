import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaWeilRepFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaWeilRepSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionsBiThetaTwoVariablesCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIteratedWeilActionBiThetaStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem biAct_all : ∀ D : D7, BiAct D := by
  intro D ψ A S A' χA χS χS' χA' oma omb ha hb C hC
  exact ⟨GlobalTheory.T.isJointlySmoothBiTheta_weilRep_first_variable D ψ A S A' χA χS oma ha C hC, GlobalTheory.T.isBiTheta_weilRep_second_variable D ψ A S A' χS' χA' omb hb C hC,
    GlobalTheory.T.weilActions_biTheta_twoVariables_commute D ψ A S A' χA χS χS' χA' oma omb ha hb C hC, GlobalTheory.T.continuous_iteratedWeilAction_biTheta D ψ A S A' χA χS χS' χA' oma omb ha hb C hC⟩

end GlobalTheory.SeeSaw

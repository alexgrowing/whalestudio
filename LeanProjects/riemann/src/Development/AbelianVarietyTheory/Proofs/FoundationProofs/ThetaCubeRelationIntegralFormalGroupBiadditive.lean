import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarAdditionFormulaPadicModelParameterStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerPadicDeterminantFormulaStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaCube

theorem cube_addInt_beBiadd : ∀ D : D7, GL3Theta.cube D ∧ GL3Theta.addInt D ∧ GL3Theta.beBiadd D := by
  intro D
  have hc : GL3Theta.cube D := Formalism.MainNotions.Ext.CutA.theorem_of_cube_of_addition_formulas D (GlobalTheory.T.sigmaStar_addition_formula_padic_modelParameter D) (GlobalTheory.T.pAdicFrobeniusStickelberger_of_d7_datum D)
  exact ⟨hc, Formalism.MainNotions.Ext.addInt_holds D, Formalism.MainNotions.Ext.beBiadd_of_cube D hc⟩

end GlobalTheory.ThetaCube

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharApplyEqAdelicChar
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardTraceAdelicAddChar_apply_eq_adelicChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ x : AF F, ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := by
  first | exact @GlobalTheory.StdCharEq.eq_adelicChar | exact GlobalTheory.StdCharEq.eq_adelicChar | (intros; apply GlobalTheory.StdCharEq.eq_adelicChar <;> assumption)

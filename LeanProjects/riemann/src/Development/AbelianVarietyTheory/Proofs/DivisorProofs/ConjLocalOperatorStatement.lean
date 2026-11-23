import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_local_operator : ∀ {F : Type} [Field F] [NumberField F] {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ), IsLocOp e → IsLocOp (conjLin e) := by
  first | exact @GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin | exact GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin | (intros; apply GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin <;> assumption)

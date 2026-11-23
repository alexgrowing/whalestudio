import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalWeilOperatorLeviBlock
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRationalWeilOperator_leviBlock : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (g h : Matrix κ κ F), gᵀ * h = 1 →
    HasOp ψ (Matrix.fromBlocks g 0 0 h) := by
  first | exact @GlobalTheory.RatWeilOp.hasOp_levi | exact GlobalTheory.RatWeilOp.hasOp_levi | (intros; apply GlobalTheory.RatWeilOp.hasOp_levi <;> assumption)

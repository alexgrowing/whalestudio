import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentHasRationalWeilOperatorQuadraticCh
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerUnipotent_hasRationalWeilOperator_quadraticChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (b : Matrix κ κ F), bᵀ = b →
    HasOp ψ (Matrix.fromBlocks 1 0 b 1) := by
  first | exact @GlobalTheory.RatWeilUnip.hasOp_unip | exact GlobalTheory.RatWeilUnip.hasOp_unip | (intros; apply GlobalTheory.RatWeilUnip.hasOp_unip <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMatrixCompositionUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_matrix_composition_unique : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (e e' e'' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), (∀ X X' Y Y', IsMat e e' X Y → IsMat e' e'' X' Y' → IsMat e e'' (X' * X) (Y' * Y)) ∧ (∀ X Y Y', IsMat e e' X Y → IsMat e e' X Y' → Y = Y') ∧ ∀ c : Ainf p O, IsMat e e (c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) ((inA c : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))) := by
  first | exact @GlobalTheory.DetInv.isMat_calculus | exact GlobalTheory.DetInv.isMat_calculus | (intros; apply GlobalTheory.DetInv.isMat_calculus <;> assumption)

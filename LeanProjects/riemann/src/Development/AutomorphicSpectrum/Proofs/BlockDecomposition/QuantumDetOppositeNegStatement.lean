import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetOppositeNeg
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_det_opposite_neg : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X → ∀ v : ℂ, MulOpposite.unop (Formalism.REAL.qdet (fun i j => MulOpposite.op (-X i j)) v) = ((-1 : ℂ) ^ n) • Formalism.REAL.qdet X ((n : ℂ) - 1 - v) := by
  first | exact @GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg | exact GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg | (intros; apply GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg <;> assumption)

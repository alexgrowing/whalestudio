import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixAdjoinTensorUnramifiedToMatrixInjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixAdjoinTensorUnramifiedToMatrix_injective : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (γ : Matrix (Fin n) (Fin n) K), 0 < r → Function.Injective (GlobalTheory.PolyTensor.phi p K n γ r) := by
  first | (exact @GlobalTheory.PolyTensor.phi_injective) | (exact GlobalTheory.PolyTensor.phi_injective) | (intros; apply GlobalTheory.PolyTensor.phi_injective <;> assumption)

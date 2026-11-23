import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflection
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
open Matrix Formalism.IndefR.Datum
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_comm_quasiReflection : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), Gᴴ = G → G.det ≠ 0 → ∀ x : Fin n → ℂ, star x ⬝ᵥ G *ᵥ x ≠ 0 → ∃ s, IsCartanInv G s ∧ ∀ c : ℂ, s * (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) = (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) * s := by
  first | exact @GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection | exact GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection | (intros; apply GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection <;> assumption)

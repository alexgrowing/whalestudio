import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoConvMulSymmetricCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bialgebraPullbackTwo_convMul_symmetricCocycle : ∀ {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B] [IsCocomm R A] (f g : A →ₐc[R] B) (c : A ⊗[R] A), c ∈ symCocycles R A → pullbackTwo (toConv f * toConv g).ofConv c = pullbackTwo f c + pullbackTwo g c + cobOne R B (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) := by
  first | exact @GlobalTheory.PDiv.pullTwo_convMul | exact GlobalTheory.PDiv.pullTwo_convMul | (intros; apply GlobalTheory.PDiv.pullTwo_convMul <;> assumption)

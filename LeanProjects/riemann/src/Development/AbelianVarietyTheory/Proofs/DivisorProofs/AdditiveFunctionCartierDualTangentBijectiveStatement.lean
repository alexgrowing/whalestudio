import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionCartierDualTangentBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveFunctionCartierDualTangent_bijective : ∀ {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A], Function.Bijective (primTangent R A) := by
  first | exact @GlobalTheory.PDiv.primTangent_bijective | exact GlobalTheory.PDiv.primTangent_bijective | (intros; apply GlobalTheory.PDiv.primTangent_bijective <;> assumption)

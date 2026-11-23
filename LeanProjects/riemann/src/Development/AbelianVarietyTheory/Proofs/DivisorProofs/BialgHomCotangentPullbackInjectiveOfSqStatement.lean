import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomCotangentPullbackInjectiveOfSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A] [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A), (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) → Function.Injective (GlobalTheory.PDiv.cotMap f) := by
  first | exact @GlobalTheory.PDiv.cotMap_injective_of_sq | exact GlobalTheory.PDiv.cotMap_injective_of_sq | (intros; apply GlobalTheory.PDiv.cotMap_injective_of_sq <;> assumption)

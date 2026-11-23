import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveWithCotangentOfDualHeightOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_with_cotangent_of_dual_height_one : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ φ ∈ augIdeal K (CartierDual K H), φ ^ p = 0) → ∀ w : Cot K H, ∃ b : H, cobOne K H b = 0 ∧ dUnit K b = w := by
  first | exact @GlobalTheory.PDiv.exists_primitive_dUnit_eq | exact GlobalTheory.PDiv.exists_primitive_dUnit_eq | (intros; apply GlobalTheory.PDiv.exists_primitive_dUnit_eq <;> assumption)

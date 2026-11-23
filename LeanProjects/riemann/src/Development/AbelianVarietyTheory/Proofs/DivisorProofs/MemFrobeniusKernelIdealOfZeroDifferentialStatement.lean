import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFrobeniusKernelIdealOfZeroDifferential
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_frobeniusKernelIdeal_of_zero_differential : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], ∀ b : H, counit (R := K) b = 0 → dUnit K b = 0 → Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (cobOne K H b) = 0 → b ∈ frobKerIdeal p K H := by
  first | exact @GlobalTheory.PDiv.FrobKerPrim.mem_frobKerIdeal_of_cobOne | exact GlobalTheory.PDiv.FrobKerPrim.mem_frobKerIdeal_of_cobOne | (intros; apply GlobalTheory.PDiv.FrobKerPrim.mem_frobKerIdeal_of_cobOne <;> assumption)

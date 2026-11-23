import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomSurjectiveIffFinrankKernelQuotientEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (f : C →ₐc[k] A), Function.Surjective f ↔ Module.finrank k (A ⧸ kerIdeal f) = 1 := by
  first | exact @GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one | exact GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one | (intros; apply GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one <;> assumption)

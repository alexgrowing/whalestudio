import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKernelIdealMulOfIdempotents
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_kernelIdeal_mul_of_idempotents : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∀ n : ℕ, Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) * Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) = p ^ (n * G.height) := by
  first | exact @GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem | exact GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem | (intros; apply GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem <;> assumption)

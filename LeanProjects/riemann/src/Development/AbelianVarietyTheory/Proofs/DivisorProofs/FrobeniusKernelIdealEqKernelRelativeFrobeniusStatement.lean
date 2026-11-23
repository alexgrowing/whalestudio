import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelIdealEqKernelRelativeFrobenius
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ), frobKerIdeal p R (G.A n) = kerIdeal ((relFrob h G).app n) := by
  first | exact @GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob | exact GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob | (intros; apply GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob <;> assumption)

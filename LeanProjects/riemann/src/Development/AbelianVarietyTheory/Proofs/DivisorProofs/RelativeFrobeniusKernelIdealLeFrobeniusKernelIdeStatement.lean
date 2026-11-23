import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ), kerIdeal ((relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) := by
  first | exact @GlobalTheory.PDiv.kerIdeal_relFrob_le_frobKerIdeal | exact GlobalTheory.PDiv.kerIdeal_relFrob_le_frobKerIdeal | (intros; apply GlobalTheory.PDiv.kerIdeal_relFrob_le_frobKerIdeal <;> assumption)

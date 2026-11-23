import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHopfIdeal_kerIdeal_of_bialgHom' : ∀ (k A B : Type) [CommRing k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] (f : B →ₐc[k] A), (kerIdeal f).IsHopfIdeal k := by
  first | exact @GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom | exact GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom | (intros; apply GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom <;> assumption)

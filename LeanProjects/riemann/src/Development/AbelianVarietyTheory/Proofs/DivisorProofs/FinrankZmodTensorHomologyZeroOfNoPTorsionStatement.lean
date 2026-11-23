import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankZmodTensorHomologyZeroOfNoPTorsion
import Mathlib
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_zmod_tensor_homology_zero_of_noPTorsion : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (x : C.X 0), (p : ℤ) • x = 0 → x = 0) → Module.Finite ℤ (C.homology 0) → Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology 0)) = Module.finrank ℤ (C.homology 0) := by
  first | exact @GlobalTheory.finrank_zmod_tensor_homology_zero | exact GlobalTheory.finrank_zmod_tensor_homology_zero | (intros; apply GlobalTheory.finrank_zmod_tensor_homology_zero <;> assumption)

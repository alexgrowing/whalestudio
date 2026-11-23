import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.IsIntegral A B → RingHom.ker (algebraMap A B) ≤ nilradical A → IsUnit (q : A) → (∀ k : ℕ, HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => B))) → HInv q A := by
  first | (exact @GlobalTheory.EtC.CechDescHInv.hInv_of_integral) | (exact GlobalTheory.EtC.CechDescHInv.hInv_of_integral) | (intros; apply GlobalTheory.EtC.CechDescHInv.hInv_of_integral  <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassFromIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_class_from_integral : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), Algebra.IsIntegral A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧ ∃ a' : Ht q (sp A') 0 (i - 1), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = gmPhi q A' i a' := by
  first | (exact @GlobalTheory.EtC.LiftWitness.lift_witness) | (exact GlobalTheory.EtC.LiftWitness.lift_witness) | (intros; apply GlobalTheory.EtC.LiftWitness.lift_witness  <;> assumption)

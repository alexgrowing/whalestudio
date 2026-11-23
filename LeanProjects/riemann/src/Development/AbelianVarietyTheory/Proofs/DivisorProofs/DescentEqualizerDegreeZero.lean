import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDescentDegreeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_equalizer_degree_zero : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'], Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) → ∀ (j : ℤ) (b : Ht q (sp A') 0 j), pull _ (spMap (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b = pull _ (spMap (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b → ∃ a : Ht q (sp A) 0 j, pull _ (spMap (algebraMap A A')) _ 0 a = b := by
  first | (exact @GlobalTheory.EtC.DescZero.desc_zero) | (exact GlobalTheory.EtC.DescZero.desc_zero) | (intros; apply GlobalTheory.EtC.DescZero.desc_zero  <;> assumption)

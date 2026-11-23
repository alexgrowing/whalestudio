import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusCharacterUnitActionProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_cohomology_injective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'], Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) → (∀ j : ℤ, Subsingleton (Ht q (sp A) 1 j)) → ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = 0 → x = 0 := by
  first | (exact @GlobalTheory.EtC.kerLaurent) | (exact GlobalTheory.EtC.kerLaurent) | (intros; apply GlobalTheory.EtC.kerLaurent  <;> assumption)

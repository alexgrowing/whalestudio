import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCPullbackBijectiveFiniteStrictlyHenselian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentC_pullback_bijective_finite_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ i : ℤ, Function.Bijective (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective) | (exact GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective) | (intros; apply GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective <;> assumption)

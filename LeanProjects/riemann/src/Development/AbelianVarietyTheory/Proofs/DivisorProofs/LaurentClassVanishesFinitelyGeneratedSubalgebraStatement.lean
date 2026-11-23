import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassVanishesFinitelyGeneratedSubalgebra
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitary
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_class_vanishes_finitely_generated_subalgebra : ∀ (q : ℕ) (A S : Type) [CommRing A] [CommRing S] [Algebra A S], IsUnit (q : A) → ∀ (n i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) n i), pull _ (spMap (laurentMap (algebraMap A S))) _ _ x = 0 → ∃ t : Finset S, pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S))))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.GmStep.KillColim.kill_colim) | (exact GlobalTheory.EtC.GmStep.KillColim.kill_colim) | (intros; apply GlobalTheory.EtC.GmStep.KillColim.kill_colim  <;> assumption)

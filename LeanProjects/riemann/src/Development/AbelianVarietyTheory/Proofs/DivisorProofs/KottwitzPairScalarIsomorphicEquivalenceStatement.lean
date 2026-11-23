import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairScalarIsomorphicEquivalence
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzPairScalarIsomorphic_equivalence : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Equivalence (Pair.Rel (G := G)) := by
  first | (exact @GlobalTheory.LKMid.Pair.rel_equivalence) | (exact GlobalTheory.LKMid.Pair.rel_equivalence) | (intros; apply GlobalTheory.LKMid.Pair.rel_equivalence  <;> assumption)

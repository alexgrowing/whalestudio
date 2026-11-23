import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.related_pairs_same_polarization : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G), P.Rel Q → Q.pol = P.pol ∧ Q.c = P.c := by
  first | (exact @GlobalTheory.LKMid.Pair.rel_pol_c) | (exact GlobalTheory.LKMid.Pair.rel_pol_c) | (intros; apply GlobalTheory.LKMid.Pair.rel_pol_c  <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtP
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_regular_image_at_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G), (∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w)) ∧ regular₂ G P.atP ∧ ∀ y : P.cent, locC G y.1 ∈ Subgroup.centralizer {P.atP} := by
  first | (exact @GlobalTheory.LKMid.atP_regular) | (exact GlobalTheory.LKMid.atP_regular) | (intros; apply GlobalTheory.LKMid.atP_regular  <;> assumption)

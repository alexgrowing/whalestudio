import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairAdelicProdUnramifiedEmbeddingInjec
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_adelicProdUnramifiedEmbedding_injective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : ℕ) (z : Gr G r), Function.Injective ((P.toAf x t hx).prod (P.toQr r z)) := by
  first | (exact @GlobalTheory.LKMid.pair_embedding_injective) | (exact GlobalTheory.LKMid.pair_embedding_injective) | (intros; apply GlobalTheory.LKMid.pair_embedding_injective  <;> assumption)

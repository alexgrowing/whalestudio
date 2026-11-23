import Formalism.RankGapBounds.GridNumericalHypotheses
import Formalism.RankGapBounds.RankGapProofs.RandomSubsetLemmaCounterexample

namespace Formalism.RankGapBounds.V4

open Formalism.RankGapBounds.LocalQuadraticParts Formalism.RankGapBounds.ExistsSmulMemTer

theorem tops_lemma_sixteen_holds : RankGapPrintedLemma := by
  intro α ι _ _ _ δ β ω BAD _ hδ0 hδ1 hq hβ hω hBAD
  exact tops_lemma_six_holds α ι δ β ω BAD hδ0 hδ1 (by linarith) hβ hω hBAD

end Formalism.RankGapBounds.V4

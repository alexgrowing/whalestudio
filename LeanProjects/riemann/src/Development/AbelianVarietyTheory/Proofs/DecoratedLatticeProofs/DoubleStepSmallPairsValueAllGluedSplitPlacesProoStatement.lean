import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepSmallPairsValueAllGluedSplitPlacesProo
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepSmallPairsValueAllGluedSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.VertexAll D := by
  first | exact @GlobalTheory.FinPl.vertexAll | exact GlobalTheory.FinPl.vertexAll | (intros; apply GlobalTheory.FinPl.vertexAll <;> assumption)

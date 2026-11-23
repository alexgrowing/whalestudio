import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.AllComb D := by
  first | exact @GlobalTheory.FinPl.allComb | exact GlobalTheory.FinPl.allComb | (intros; apply GlobalTheory.FinPl.allComb <;> assumption)

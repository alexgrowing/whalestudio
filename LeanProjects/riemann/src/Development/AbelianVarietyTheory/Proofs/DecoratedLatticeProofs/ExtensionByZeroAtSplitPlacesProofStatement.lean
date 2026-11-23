import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroAtSplitPlacesProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extensionByZeroAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.ExtAll D := by
  first | exact @GlobalTheory.FinPl.ExtAllPf.ext_all | exact GlobalTheory.FinPl.ExtAllPf.ext_all | (intros; apply GlobalTheory.FinPl.ExtAllPf.ext_all <;> assumption)

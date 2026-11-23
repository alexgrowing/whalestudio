import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.threeOrbits_gluedCore_atPlace : ∀ D : D7, GlobalTheory.FinPl.OrbitGlued D := by
  first | exact @GlobalTheory.FinPl.orbitGlued | exact GlobalTheory.FinPl.orbitGlued | (intros; apply GlobalTheory.FinPl.orbitGlued <;> assumption)

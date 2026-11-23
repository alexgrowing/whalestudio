import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordJumpsInWindows
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_jumps_in_windows : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T1 ∧ ∀ i, ∀ u ∈ (pageWord L j ε τ φ).J1 i, -((pageWord L j ε τ φ).Mi i : ℤ) ≤ u ∧ u ≤ (pageWord L j ε τ φ).hi i := by
  first | exact @GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy | exact GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy | (intros; apply GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy <;> assumption)

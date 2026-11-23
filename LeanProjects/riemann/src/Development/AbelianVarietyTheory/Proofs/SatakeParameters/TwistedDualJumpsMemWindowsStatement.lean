import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindows
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualJumps_mem_windows : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (S η : ℝ), (∀ i, 0 ≤ ((P.v i : ℚ) : ℝ) ∧ ((P.v i : ℚ) : ℝ) ≤ S) → (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ∀ u ∈ jT1 P j s, (if (!s) = true then szT P j s ≤ u ∧ u ≤ szT P j s + (⌊S⌋₊ : ℕ) else -szT P j s - (⌊S⌋₊ : ℕ) ≤ u ∧ u ≤ -szT P j s) ∨ |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  first | exact @GlobalTheory.jT1_mem_window_of_bounded_v | exact GlobalTheory.jT1_mem_window_of_bounded_v | (intros; apply GlobalTheory.jT1_mem_window_of_bounded_v <;> assumption)

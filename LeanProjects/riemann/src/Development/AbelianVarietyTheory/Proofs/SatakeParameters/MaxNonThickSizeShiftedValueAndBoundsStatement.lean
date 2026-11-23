import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxNonThickSizeShiftedValueAndBounds
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (wHat D : ℝ) = wMax D + ((D.R.t : ℝ) + 1) / 2 ∧ (wHat D : ℝ) + (L.etaSz + D.R.t + 2) ≤ 2 * L.sc.b' ∧ (wHat D : ℝ) + sHat L + etaHat L + 1 ≤ 2 * L.sc.b' := by
  first | exact @GlobalTheory.HTW.wHat_le | exact GlobalTheory.HTW.wHat_le | (intros; apply GlobalTheory.HTW.wHat_le <;> assumption)

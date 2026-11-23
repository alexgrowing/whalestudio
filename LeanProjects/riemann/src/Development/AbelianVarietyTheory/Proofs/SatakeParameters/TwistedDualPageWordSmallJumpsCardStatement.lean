import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordSmallJumpsCard
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pageWord_T2_and_J2_card_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T2 ∧ ∀ i, ((pageWord L j ε τ φ).J2 i).card = D.R.r ∧ (((pageWord L j ε τ φ).J2 i).filter fun u : ℤ => |u| ≤ (etaHat L : ℤ)).card = D.R.m := by
  first | exact @GlobalTheory.HTW.twistedDualPageWord_small_jumps_card | exact GlobalTheory.HTW.twistedDualPageWord_small_jumps_card | (intros; apply GlobalTheory.HTW.twistedDualPageWord_small_jumps_card <;> assumption)

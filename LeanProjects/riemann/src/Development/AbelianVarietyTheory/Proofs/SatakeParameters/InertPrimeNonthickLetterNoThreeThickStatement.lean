import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNonthickLetterNoThreeThick
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrime_nonthick_letter_no_three_thick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 3 ≤ H.Lw → φ.1.2 = -1 → ¬ (φ = R.cc ∧ Thick H τ) → NoThree (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) ∧ ∃ i : ZMod (orderOf φ), ¬ Thick H (letter τ φ i) := by
  first | exact @GlobalTheory.HTW.InertWord.inert_nothree_nonthick | exact GlobalTheory.HTW.InertWord.inert_nothree_nonthick | (intros; apply GlobalTheory.HTW.InertWord.inert_nothree_nonthick <;> assumption)

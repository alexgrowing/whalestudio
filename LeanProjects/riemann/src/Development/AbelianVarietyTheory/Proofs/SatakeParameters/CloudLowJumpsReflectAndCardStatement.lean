import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CloudLowJumpsReflectAndCard
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cloudLowJumps_reflect_and_card : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m), jR P j false = (jR P j true).map (fun u => (R.t : ℤ) - 1 - u) ∧ ∀ s, (jW P j s).card = R.r ∧ (jR P j s).card = R.nV ∧ (jT2 P j s).card = R.r ∧ jT2 P j s ≤ jT1 P j s := by
  first | exact @GlobalTheory.HTW.jR_symm_card | exact GlobalTheory.HTW.jR_symm_card | (intros; apply GlobalTheory.HTW.jR_symm_card <;> assumption)

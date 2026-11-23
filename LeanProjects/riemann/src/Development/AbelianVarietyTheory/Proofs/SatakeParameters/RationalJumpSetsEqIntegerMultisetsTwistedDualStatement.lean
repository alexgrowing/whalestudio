import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalJumpSetsEqIntegerMultisetsTwistedDual
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalJumpSets_eq_integerMultisets_twistedDual : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) (g : D.R.GG) (ep up : Bool), LJ.PlaceOf D ρ g → (up = true ↔ LJ.TypeU D ep g) → ∀ a : ℤ, ((a : ℚ) ∈ LJ.dualS (LJ.JJ D up (D.nd.j i) ρ) ↔ a ∈ jT1 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) ∧ ((a : ℚ) ∈ LJ.dualS (LJ.JW D up (D.nd.j i) ρ) ↔ a ∈ jT2 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) := by
  first | exact @GlobalTheory.HTW.Rec.rat_jump_sets_eq_int_multisets | exact GlobalTheory.HTW.Rec.rat_jump_sets_eq_int_multisets | (intros; apply GlobalTheory.HTW.Rec.rat_jump_sets_eq_int_multisets <;> assumption)

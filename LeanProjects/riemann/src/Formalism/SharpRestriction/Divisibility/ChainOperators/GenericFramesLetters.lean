import Formalism.SharpRestriction.Divisibility.ChainOperators.WeightFramesOfSubgroupFrames
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GenFrameSB

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV.Lemmas

theorem cutKW_holds : CutKW.KW := kw_of_cutSB coeffNormLE_iff_spanNormLE_of_hasCompl

theorem theta_isometry_facts_hold (D : D7) : Formalism.MainNotions.OrbitPlaces.ConclusionW D := by
  intro l _ N0 N1 nu Th B
  apply cutKW_holds

theorem generic_frames_letters : Formalism.MainNotions.product_zeroth_first_parts.Conclusion4 := by
  intro l _ d _ N0 N1 nu Th B
  apply cutKW_holds

theorem stmtW_holds (D : D7) : Formalism.MainNotions.OrbitPlaces.WeightsFromStandardBasis D := fun _ => theta_isometry_facts_hold D

end Formalism.MainNotions.DIV.Lemmas

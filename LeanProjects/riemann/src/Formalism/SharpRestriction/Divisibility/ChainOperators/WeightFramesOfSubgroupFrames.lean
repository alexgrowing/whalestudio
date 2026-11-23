import Formalism.PeriodIntegrals.NablaSpans.ExpansionCoeffValuationGe
import Formalism.PeriodIntegrals.NablaSpans.MinorProdSpanHasCompl
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinorSpanCompl

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV.Lemmas

theorem weight_frames_of_generic_frames (h : CutKW.KW) (D : D7) : Formalism.MainNotions.OrbitPlaces.ConclusionW D := by
  intro l _ N0 N1 nu Th B
  classical
  exact h _ l N0 N1 nu Th B

theorem generic_frames_cyclic_letters (h : CutKW.KW) : Formalism.MainNotions.product_zeroth_first_parts.Conclusion4 := by
  intro l _ d _ N0 N1 nu Th B
  exact h (ZMod d) l N0 N1 nu Th B

theorem stmtW_of_cut (h : CutKW.KW) (D : D7) : Formalism.MainNotions.OrbitPlaces.WeightsFromStandardBasis D := fun _ => weight_frames_of_generic_frames h D

theorem kw_of_cutSB (h : CutKW.KWsb) : CutKW.KW := h minor_span_complement

theorem weight_frames_of_subgroup_frames (h : CutKW.KWsb) (D : D7) : Formalism.MainNotions.OrbitPlaces.ConclusionW D := weight_frames_of_generic_frames (kw_of_cutSB h) D

end Formalism.MainNotions.DIV.Lemmas

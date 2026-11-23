import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWbGlue

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB Formalism.L2.SG.Pf.GE

theorem bruhatHaar_of_sandwich_volLim (hS : Sandwich) (hV : VolLim) : BruhatHaar :=
  bruhatHaar_of_rhsHaar rhsHaar gaugeShift hS hV

theorem wbHaar_of_rhsWLim (hL : RhsWLim) : WbHaar :=
  wbHaar_of_rhsWHaar rhsWHaar gaugeShiftW hL

theorem gaugeExists_of_sandwich_rhsWLim (hS : Sandwich) (hV : VolLim) (hU : ExistsGaugeMeasureForEachRank) (hL : RhsWLim) : GaugeExists :=
  gaugeExists_of rhsHaar rhsWHaar wbDataEx hU gaugeShift gaugeShiftW (rhsLim_of hS hV) hL

theorem jacGauge_of_sandwich_gaugeMeasure (hS : Sandwich) (hV : VolLim) (hU : ExistsGaugeMeasureForEachRank) (hL : RhsWLim) : JacGauge :=
  jacGauge_of (bruhatHaar_of_sandwich_volLim hS hV) (wbHaar_of_rhsWLim hL) (gaugeExists_of_sandwich_rhsWLim hS hV hU hL)

end Formalism.L2.SG.Pf

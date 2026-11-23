import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolKap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol MeasureTheory

theorem typFacts_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u u' : D.what₂.Word) : TypFacts X u u' := by
  apply typFacts_of (h1 := gSplitX_holds X) (h3 := Formalism.L2.SG.LocVolKap.kapX X hb u u')
  exact tCongX X u u'

end Formalism.L2.SG.Pf

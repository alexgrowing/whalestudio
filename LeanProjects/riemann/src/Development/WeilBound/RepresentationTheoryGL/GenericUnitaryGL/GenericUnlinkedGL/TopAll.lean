import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.ExistsEquivOfMapUnivEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerHeredity.Replay
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.CuspidalGenericity.Bridge

namespace GlobalTheory.RgGu

theorem genericUnique (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GenericUnique k :=
  genericUnique_of PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (PositivityTheory.rg.gu.hered2.whitHeredity_all k)
    (PositivityTheory.rg.gu.whit.whitRankIrr k) (GlobalTheory.BZSeg.Cusp.cuspGeneric k)

end GlobalTheory.RgGu

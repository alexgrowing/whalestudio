import Development.WeilBound.CoreStatements.AutomorphicKernels.RamifiedExponentBounds.LocalSpreadOfLocalExpBound
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.ExpBound
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.IsGenericOfEquiv
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

namespace PositivityTheory.JsR

theorem localExpBound_holds : LocalExpBound := by
  intro k _ _ _ _ _ N V _ _ π hs hi hu hg
  obtain ⟨h, δ, Δ, s, hΔ, hc, hb, hd⟩ := PositivityTheory.RgUd.Exp.genUnitCCOf PositivityTheory.RgUd.expBound GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds
    k N V π hs hi hu hg
  exact ⟨h, δ, Δ, s, hΔ, fun j _ hω z => PositivityTheory.RgUd.UOrder.log_norm_centralChar_u (hΔ j) (hc j) hω z, hb, hd⟩

theorem localSpread_holds : LocalSpread := localSpread_of_localExpBound localExpBound_holds

end PositivityTheory.JsR

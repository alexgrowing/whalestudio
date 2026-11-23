import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.StepForm
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnipotentBounds.UnipBLeDerUnipOne

namespace PositivityTheory.RgUd.Form.Final

theorem besselSum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.BesselSum k :=
  PositivityTheory.RgUd.Form.Asm.asmForm k (PositivityTheory.RgUd.Form.LeviSmoothness.Final.stepForm k)

end PositivityTheory.RgUd.Form.Final

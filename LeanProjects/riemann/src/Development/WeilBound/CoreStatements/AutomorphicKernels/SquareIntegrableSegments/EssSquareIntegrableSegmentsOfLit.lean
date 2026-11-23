import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.Development
import Development.WeilBound.CoreStatements.PublishedTheorems.LanglandsClassification.Bridge
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

noncomputable section

namespace PositivityTheory.PfEss

theorem essSquareIntegrableSegments_main (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSocleGL k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegExists k)
    (hJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegJacquet k) : GlobalTheory.Published.EssSquareIntegrableSegments :=
  essSquareIntegrableSegments_of hE PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hF hS hL hJ

end PositivityTheory.PfEss

end

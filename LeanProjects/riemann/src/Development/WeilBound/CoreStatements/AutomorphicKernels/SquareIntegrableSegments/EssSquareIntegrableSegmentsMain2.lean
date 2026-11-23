import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.EssSquareIntegrableSegmentsOfLit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFreeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissibleStatement

noncomputable section

namespace PositivityTheory.PfEss

theorem lSocleGL_of_orderFree (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hO : Zc.LOrderFree k) : Zc.LSocleGL k :=
  GlobalTheory.T.langlands_socle_of_order_free PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (GlobalTheory.T.local_langlands_of_irreducible_admissible PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top) hO

theorem essSquareIntegrableSegments_main2 (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LOrderFree k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegExists k)
    (hJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegJacquet k) : GlobalTheory.Published.EssSquareIntegrableSegments :=
  essSquareIntegrableSegments_main hE hF (fun k _ _ _ _ _ => lSocleGL_of_orderFree k (hO k)) hL hJ

end PositivityTheory.PfEss

end

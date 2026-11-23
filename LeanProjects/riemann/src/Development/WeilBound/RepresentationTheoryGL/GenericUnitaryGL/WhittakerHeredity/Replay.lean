import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity
open GlobalTheory.BZMir.Leib

namespace PositivityTheory.rg.gu.hered2

theorem whitHeredity_all :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      WhitHeredity k :=
  fun k _ _ _ _ => GlobalTheory.CompanionTheory.Rodier.whitHeredity k

end PositivityTheory.rg.gu.hered2

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], WhitHeredity k := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.whitHeredity | exact GlobalTheory.CompanionTheory.Rodier.whitHeredity | (intros; apply GlobalTheory.CompanionTheory.Rodier.whitHeredity <;> assumption)

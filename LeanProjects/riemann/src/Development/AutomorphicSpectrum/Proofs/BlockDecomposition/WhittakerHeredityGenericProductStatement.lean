import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProduct
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_heredity_generic_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], WhitHeredity k → GenericProdIff k := by
  first | exact @GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | exact GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | (intros; apply GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockIntertwinersSpan
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_two_block_intertwiners_span : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    ⨆ f : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)), LinearMap.range f.toLinearMap = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.whit_iSup_range_eq_top | exact GlobalTheory.CompanionTheory.BZNuPair.whit_iSup_range_eq_top | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.whit_iSup_range_eq_top <;> assumption)

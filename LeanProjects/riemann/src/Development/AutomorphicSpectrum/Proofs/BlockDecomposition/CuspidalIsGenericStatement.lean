import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_is_generic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π := by
  first | exact @GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal | exact GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal | (intros; apply GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal <;> assumption)

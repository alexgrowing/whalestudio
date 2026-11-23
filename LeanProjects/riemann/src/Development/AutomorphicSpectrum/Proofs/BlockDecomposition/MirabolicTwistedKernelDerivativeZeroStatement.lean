import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZero
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), twKer τ (MirUin k n) 1 = twKer τ (derUnipM k n n) (derCharM k ψ n n) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM | exact GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM | (intros; apply GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM <;> assumption)

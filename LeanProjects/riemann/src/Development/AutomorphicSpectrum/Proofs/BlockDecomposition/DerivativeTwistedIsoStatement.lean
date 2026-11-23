import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_twisted_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (j n : ℕ) (π : GRep k (n + j)), GIso (derivB ψ j π) ((dG ψ j π).tw ((j : ℝ) / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw | exact GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.DerivTw.derivB_iso_tw <;> assumption)

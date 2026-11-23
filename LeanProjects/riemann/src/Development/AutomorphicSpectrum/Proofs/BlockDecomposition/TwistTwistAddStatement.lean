import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistTwistAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_twist_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : GRep k n) (s s' : ℝ), GIso ((A.tw s).tw s') (A.tw (s + s')) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw | exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw <;> assumption)

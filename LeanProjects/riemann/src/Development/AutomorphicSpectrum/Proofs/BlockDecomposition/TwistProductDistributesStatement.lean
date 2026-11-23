import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistProductDistributes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_product_distributes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (A : GRep k r) (B : GRep k t) (s : ℝ), GIso ((A.prod B).tw s) ((A.tw s).prod (B.tw s)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod | exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod <;> assumption)

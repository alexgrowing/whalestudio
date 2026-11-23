import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentNormal
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_unipotent_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), (MirUin k n).Normal := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirUin_normal | exact GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirUin_normal | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirUin_normal <;> assumption)

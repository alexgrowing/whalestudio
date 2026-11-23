import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentLeParabolic
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_unipotent_le_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), MirUin k (m + j) ≤ MirabolicParabolic k m j := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.mirUin_le_HGP | exact GlobalTheory.CompanionTheory.LeibPhi.mirUin_le_HGP | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.mirUin_le_HGP <;> assumption)

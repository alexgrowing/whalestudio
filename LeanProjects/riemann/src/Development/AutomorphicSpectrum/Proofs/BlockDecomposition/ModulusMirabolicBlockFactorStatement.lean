import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusMirabolicBlockFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_mirabolic_block_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : ℝ) (h : MirabolicParabolic k (i + 1) t), dpowM ((i + 1) + t) s (h : Mir k ((i + 1) + t)) = dpow (i + 1) s (gpProj k (i + 1) t h).1 * dpow (t + 1) s (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.dpowM_hgp | exact GlobalTheory.CompanionTheory.BZPhiPG.dpowM_hgp | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.dpowM_hgp <;> assumption)

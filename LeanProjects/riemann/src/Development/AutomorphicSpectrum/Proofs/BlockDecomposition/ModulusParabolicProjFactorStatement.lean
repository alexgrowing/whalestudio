import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusParabolicProjFactor
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_parabolic_proj_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (s : ℝ) (h : MirabolicParabolic k m j),
    dpowM (m + j) s (h : Mir k (m + j)) = dpow m s (gpProj k m j h).1 * dpowM j s (gpProj k m j h).2 := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp | exact GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp <;> assumption)

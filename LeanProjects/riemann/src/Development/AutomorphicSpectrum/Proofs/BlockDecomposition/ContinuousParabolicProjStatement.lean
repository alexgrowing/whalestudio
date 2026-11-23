import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousParabolicProj
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi | exact GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi <;> assumption)

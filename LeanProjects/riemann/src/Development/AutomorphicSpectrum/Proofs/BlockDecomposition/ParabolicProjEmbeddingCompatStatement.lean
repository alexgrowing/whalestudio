import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjEmbeddingCompat
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_proj_embedding_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (y : MirabolicParabolic k m j) (hh : embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1)),
    gpProj k m (j + 1) ⟨_, hh⟩ = ((gpProj k m j y).1, embedding₂ k j (gpProj k m j y).2) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.IotaProj.gpProj_iotaM | exact GlobalTheory.CompanionTheory.LeibPhi.IotaProj.gpProj_iotaM | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.IotaProj.gpProj_iotaM <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedParabolicMulEmbeddedMirabolic
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_parabolic_mul_embedded_mirabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ),
    IsClosed {g : Mir k (m + (j + 1)) | ∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x} := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Closed.isClosed_HGP_iota | exact GlobalTheory.CompanionTheory.LeibPhi.Closed.isClosed_HGP_iota | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Closed.isClosed_HGP_iota <;> assumption)

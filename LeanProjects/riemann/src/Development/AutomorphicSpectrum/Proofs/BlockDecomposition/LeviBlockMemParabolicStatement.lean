import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolic
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_block_mem_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t), ∃ h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t, pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj | exact GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj <;> assumption)

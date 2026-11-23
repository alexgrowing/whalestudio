import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTwistInducedMemFullRankSpace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_twist_induced_mem_full_rank_space : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (hnd : n ≤ d) (ν : kˣ →* ℂˣ)
    (F : IndSp (pairPlace (b2 n d) (block_size_pair_sum hnd)) (ofChar (pairChar k (b2 n d) (chi2 k ν)))),
    GlobalTheory.FullRankCoinv.IndTwist.detTw d (-((n : ℂ) / 2)) F.1.1 ∈ GlobalTheory.FullRankCoinv.indSp k n d ν := by
  first | exact @GlobalTheory.IndJacBlock.Bwd.bwd | exact GlobalTheory.IndJacBlock.Bwd.bwd | (intros; apply GlobalTheory.IndJacBlock.Bwd.bwd <;> assumption)

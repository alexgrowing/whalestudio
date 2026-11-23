import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedDetTwistPairCharacter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_det_twist_pair_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (hnd : n ≤ d) (ν : kˣ →* ℂˣ), ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν,
    ∃ F : IndSp (pairPlace (b2 n d) (block_size_pair_sum hnd)) (ofChar (pairChar k (b2 n d) (chi2 k ν))),
      F.1.1 = GlobalTheory.FullRankCoinv.IndTwist.detTw d ((n : ℂ) / 2) f := by
  first | exact @GlobalTheory.IndJacBlock.exists_indSp_detTw | exact GlobalTheory.IndJacBlock.exists_indSp_detTw | (intros; apply GlobalTheory.IndJacBlock.exists_indSp_detTw <;> assumption)

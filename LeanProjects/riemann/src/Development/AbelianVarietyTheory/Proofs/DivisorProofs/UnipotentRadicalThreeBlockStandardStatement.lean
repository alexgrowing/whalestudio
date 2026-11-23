import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalThreeBlockStandard
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_three_block_standard : ∀ (k : Type) [Field k] (d : ℕ) (h2 : 2 ≤ d) (u : GL (Fin d) k),
    u ∈ unipRad k (place3 h2) → GlobalTheory.JacBlock₂.IsUnipStd u := by
  first | exact @GlobalTheory.UnipRadThree.isUnipStd_of_mem_unipRad | exact GlobalTheory.UnipRadThree.isUnipStd_of_mem_unipRad | (intros; apply GlobalTheory.UnipRadThree.isUnipStd_of_mem_unipRad <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLeviEmbeddingModularCharacter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_levi_embedding_modular_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (h2 : 2 ≤ d) (x : kˣ),
    leviEmb k (place3 h2) (tor3 k d (x, 1)) = GlobalTheory.JacBlock₂.diagFirst x ∧
    (deltaHalf k (fun j : Fin 3 => Fin (sz3 d j)) (tor3 k d (x, 1)) : ℂ) = GlobalTheory.SplitFlip.apow x (((d : ℂ) - 1) / 2) := by
  first | exact @GlobalTheory.IndJacBlock.torus_levi_embedding_modulus_half | exact GlobalTheory.IndJacBlock.torus_levi_embedding_modulus_half | (intros; apply GlobalTheory.IndJacBlock.torus_levi_embedding_modulus_half <;> assumption)

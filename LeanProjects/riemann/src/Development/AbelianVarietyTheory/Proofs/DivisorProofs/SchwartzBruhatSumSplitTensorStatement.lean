import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSumSplitTensor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_sum_split_tensor : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → Af F) → ℂ), g ∈ SB (κ ⊕ κ' → Af F) → ∃ (m : ℕ) (a : Fin m → (κ → Af F) → ℂ) (b : Fin m → (κ' → Af F) → ℂ), (∀ j, a j ∈ SB (κ → Af F)) ∧ (∀ j, b j ∈ SB (κ' → Af F)) ∧ ∀ x x', g (Sum.elim x x') = ∑ j, a j x * b j x' := by
  first | exact @GlobalTheory.SBBlocks.sum_prod_blocks | exact GlobalTheory.SBBlocks.sum_prod_blocks | (intros; apply GlobalTheory.SBBlocks.sum_prod_blocks <;> assumption)

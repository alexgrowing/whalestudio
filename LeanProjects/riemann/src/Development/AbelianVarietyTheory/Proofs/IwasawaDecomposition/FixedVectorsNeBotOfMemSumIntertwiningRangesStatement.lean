import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedVectors_ne_bot_of_mem_sum_intertwining_ranges : ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X] {ι : Type} [Finite ι] {σ : Representation ℂ G V}, σ.IsIrreducible → ∀ {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X}, f ∈ ⨆ j, LinearMap.range (T j).toLinearMap → f ≠ 0 → (∀ k ∈ K, ρ k f = f) → GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
  first | exact @GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range | exact GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range | (intros; apply GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range <;> assumption)

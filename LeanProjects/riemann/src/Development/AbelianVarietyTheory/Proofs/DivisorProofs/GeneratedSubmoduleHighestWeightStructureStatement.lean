import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedSubmoduleHighestWeightStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_submodule_highest_weight_structure : ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v →
    FiniteDimensional ℂ (GlobalTheory.BlockReps.gen M.act v) ∧
    IsKLieAct (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ∧
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) μ) ∧
    IsHW (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) Λ ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ ∧
    GlobalTheory.BlockReps.gen (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ = ⊤ := by
  first | exact @GlobalTheory.GenHW.block_span_hw | exact GlobalTheory.GenHW.block_span_hw | (intros; apply GlobalTheory.GenHW.block_span_hw <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_iff_symmetricPosition_entry_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (g : GL (Fin κ ⊕ Fin (s + 1)) k), g ∈ S.P.J ↔ g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  first | exact @GlobalTheory.SymChain.SymData.mem_J_iff_pattern | exact GlobalTheory.SymChain.SymData.mem_J_iff_pattern | (intros; apply GlobalTheory.SymChain.SymData.mem_J_iff_pattern <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentDoubleCosetCellFiniteDisjointIUnion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentDoubleCosetCell_finite_disjoint_iUnion : ∀ {F : Type} [NormedField F] {n : ℕ} (B B' : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B' : Set (GL (Fin n) F)) → B' ≤ B → ∀ h₀ : GL (Fin n) F, ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F))) ∧ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F))) ∧ (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F)) := by
  first | (exact @GlobalTheory.JSW.Cut.cell_finite_disjoint_union') | (exact GlobalTheory.JSW.Cut.cell_finite_disjoint_union') | (intros; apply GlobalTheory.JSW.Cut.cell_finite_disjoint_union'  <;> assumption)

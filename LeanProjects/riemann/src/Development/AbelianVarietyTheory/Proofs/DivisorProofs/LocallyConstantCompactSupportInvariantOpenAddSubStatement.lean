import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantCompactSupportInvariantOpenAddSub
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openAddSubgroup_invariant_of_locallyConstant : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [NonarchimedeanAddGroup X] (g : X → ℂ), IsLocallyConstant g → HasCompactSupport g → ∃ H : OpenAddSubgroup X, ∀ z, ∀ a ∈ H, g (z + a) = g z := by
  first | exact @GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup | exact GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup | (intros; apply GlobalTheory.locallyConstant_compactSupport_invariant_openAddSubgroup <;> assumption)

import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace P_Jone

theorem inPow_zero (c : ℕ) : InPow c (0 : k) :=
  ⟨0, zero_mem _, map_zero _⟩

end P_Jone

theorem step_Jone {n : ℕ} (G : Grp k n) : G.JacquetOneProp := by
  refine ⟨⟨Subgroup.one_mem _, fun i j hij => ?_⟩, fun g hg => ⟨hg.1, fun i j hij => ?_⟩⟩
  · have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    rw [Units.val_one, Matrix.one_apply_ne hne]
    exact P_Jone.inPow_zero _
  · rw [(mem_parab.1 hg.2) i j hij]
    exact P_Jone.inPow_zero _

end Grp

end UpperTheory.TNZ

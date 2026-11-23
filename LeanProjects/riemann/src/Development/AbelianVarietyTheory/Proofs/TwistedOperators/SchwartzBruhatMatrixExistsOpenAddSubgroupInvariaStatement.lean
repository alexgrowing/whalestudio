import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_matrix_exists_open_addSubgroup_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [Fintype b], ∀ Φ ∈ SB (Matrix a b k), ∃ Λ : AddSubgroup (Matrix a b k), IsOpen (Λ : Set (Matrix a b k)) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  first | exact @GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup | exact GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup | (intros; apply GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup <;> assumption)

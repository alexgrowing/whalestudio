import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigEqZeroOfMemAugOfNotIntertwine
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_mem_aug_of_isEig_of_not_intertwine : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N : Set G) (θ : G → ℂ), Datum J θ → Datum N (fun _ => 1) → (∀ y ∈ N, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → ∀ u ∈ aug π N (fun _ => 1), IsEig π J θ u → u = 0 := by
  first | exact @GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine | exact GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine | (intros; apply GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelMemTwistedSpanFiniteStage
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedJacquetKernel_mem_twistedSpan_finite_stage : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (U : Subgroup G) (N : ℕ → Set G), Monotone N → (∀ y ∈ U, ∃ m, y ∈ N m) → ∀ v ∈ twKer π U 1, ∃ m, v ∈ aug π (N m) (fun _ => 1) := by
  first | exact @GlobalTheory.PsType.twKer_one_mem_aug_stage | exact GlobalTheory.PsType.twKer_one_mem_aug_stage | (intros; apply GlobalTheory.PsType.twKer_one_mem_aug_stage <;> assumption)

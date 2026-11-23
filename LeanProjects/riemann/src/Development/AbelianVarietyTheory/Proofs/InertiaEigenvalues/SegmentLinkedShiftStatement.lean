import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentLinkedShift
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_linked_shift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ), (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one | exact GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one | (intros; apply GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one <;> assumption)

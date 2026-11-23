import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSurjHomZmodOfIsPGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surjective_hom_zmod_of_isPGroup : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] [Nontrivial G], IsPGroup p G → ∃ χ : G →* Multiplicative (ZMod p), Function.Surjective χ := by
  first | exact @GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup | exact GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup | (intros; apply GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup <;> assumption)

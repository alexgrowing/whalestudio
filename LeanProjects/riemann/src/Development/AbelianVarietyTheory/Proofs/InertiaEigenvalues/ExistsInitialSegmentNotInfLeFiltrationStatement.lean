import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltration
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_initialSegment_not_inf_le_filtration : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G), Antitone R → (∃ m, R m = ⊥) → ∃ n : ℕ, ∀ t, t < n ↔ ¬ A ⊓ R t ≤ B := by
  first | exact @GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le | exact GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le | (intros; apply GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le <;> assumption)

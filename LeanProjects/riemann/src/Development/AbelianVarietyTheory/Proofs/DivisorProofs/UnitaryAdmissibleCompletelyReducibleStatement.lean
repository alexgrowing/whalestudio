import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdmissibleCompletelyReducible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
open GlobalTheory.ThK.SplitInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_admissible_completely_reducible : ∀ (H : Type) [Group H] (G₀ : Subgroup H) (S : Submodule ℂ (H → ℂ)) (𝒦 : Set (Subgroup H)), RStable G₀ S → SmAdm G₀ S 𝒦 → Unitary G₀ S → CompRed G₀ S := by
  first | exact @GlobalTheory.ThK.SplitInv.compRed_of_unitary | exact GlobalTheory.ThK.SplitInv.compRed_of_unitary | (intros; apply GlobalTheory.ThK.SplitInv.compRed_of_unitary <;> assumption)

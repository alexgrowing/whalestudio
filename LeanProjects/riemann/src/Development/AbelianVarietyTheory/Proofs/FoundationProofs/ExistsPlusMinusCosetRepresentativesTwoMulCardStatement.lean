import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlusMinusCosetRepresentativesTwoMulCard
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_plusMinusCosetRepresentatives_two_mul_card : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → (-1 : SL(2, ℤ)) ∉ Γ → ∃ (r : ℕ) (s : Fin r → SL(2, ℤ)), IsReps Γ s ∧ 2 * r = Γ.index := by
  first | exact @GlobalTheory.OddFrame.reps_index | exact GlobalTheory.OddFrame.reps_index | (intros; apply GlobalTheory.OddFrame.reps_index <;> assumption)

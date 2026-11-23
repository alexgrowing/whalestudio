import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesToSmallerOddWeightOfLeadingCoeffMatrixDet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducesToSmallerOddWeight_of_leadingCoeffMatrix_det_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det = 0 → Reduces Γ w F := by
  first | exact @GlobalTheory.OddFrame.reduces_of_det_leadM_eq_zero | exact GlobalTheory.OddFrame.reduces_of_det_leadM_eq_zero | (intros; apply GlobalTheory.OddFrame.reduces_of_det_leadM_eq_zero <;> assumption)

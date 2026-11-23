import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeMulCardOddFrameWeightsDvdThree
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.three_mul_card_oddFrame_weights_dvd_three : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (evM s w F ρ).det ≠ 0 → 3 * (Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card = r := by
  first | exact @GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd | exact GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd | (intros; apply GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd <;> assumption)

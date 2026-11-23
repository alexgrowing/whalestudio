import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddWeightFrameDetNeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_odd_weight_frame_det_ne_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (τ₀ : ℍ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → (-1 : SL(2, ℤ)) ∉ Γ → IsReps Γ s → (∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ), (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) → (∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) → c = 0) → ∃ (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧ (evM s w F τ₀).det ≠ 0 := by
  first | exact @GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero | exact GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero | (intros; apply GlobalTheory.OddFrame.exists_odd_det_evM_ne_zero <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashSubQExpansionPartialSumIsBigO
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slash_sub_qExpansion_partialSum_isBigO : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → ∀ x : SL(2, ℤ), (fun τ : ℍ => (f ∣[k] x) τ - ∑ n ∈ Finset.range M, co M k f x n * Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ n) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  first | exact @GlobalTheory.OddFrame.slash_sub_partialSum_isBigO | exact GlobalTheory.OddFrame.slash_sub_partialSum_isBigO | (intros; apply GlobalTheory.OddFrame.slash_sub_partialSum_isBigO <;> assumption)

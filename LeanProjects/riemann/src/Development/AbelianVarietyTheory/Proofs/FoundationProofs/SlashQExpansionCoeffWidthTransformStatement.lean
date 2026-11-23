import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashQExpansionCoeffWidthTransform
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slashQExpansionCoeffWidth_transform : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → (∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (x * ModularGroup.T) n = Complex.exp (2 * Real.pi * Complex.I / M) ^ n * co M k f x n) ∧ (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (γ * x) n = co M k f x n) ∧ (Odd k → ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (-x) n = -co M k f x n) := by
  first | exact @GlobalTheory.OddFrame.co_transform | exact GlobalTheory.OddFrame.co_transform | (intros; apply GlobalTheory.OddFrame.co_transform <;> assumption)

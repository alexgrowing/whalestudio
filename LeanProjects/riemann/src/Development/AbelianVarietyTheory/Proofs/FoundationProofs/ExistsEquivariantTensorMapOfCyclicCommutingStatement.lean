import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEquivariantTensorMapOfCyclicCommuting
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_tensor_map_of_cyclic_commuting : ∀ (p q r s : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ V), (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → ∀ (M₁ : GKMod p q) (M₂ : GKMod r s) (i₁ : M₁.V →ₗ[ℂ] V) (i₂ : M₂.V →ₗ[ℂ] V), (∀ Z x, i₁ (M₁.act Z x) = a₁ Z (i₁ x)) → (∀ Z y, i₂ (M₂.act Z y) = a₂ Z (i₂ y)) → ∀ (x₀ : M₁.V) (y₀ : M₂.V), genSub M₁.act {x₀} = ⊤ → genSub M₂.act {y₀} = ⊤ → i₁ x₀ = i₂ y₀ → ∃ I : M₁.V ⊗[ℂ] M₂.V →ₗ[ℂ] V, (∀ Z x y, a₁ Z (I (x ⊗ₜ y)) = I (M₁.act Z x ⊗ₜ y)) ∧ (∀ Z x y, a₂ Z (I (x ⊗ₜ y)) = I (x ⊗ₜ M₂.act Z y)) ∧ (∀ x, I (x ⊗ₜ y₀) = i₁ x) ∧ ∀ y, I (x₀ ⊗ₜ y) = i₂ y := by
  first | exact @GlobalTheory.FockBilin.exists_bilin | exact GlobalTheory.FockBilin.exists_bilin | (intros; apply GlobalTheory.FockBilin.exists_bilin <;> assumption)

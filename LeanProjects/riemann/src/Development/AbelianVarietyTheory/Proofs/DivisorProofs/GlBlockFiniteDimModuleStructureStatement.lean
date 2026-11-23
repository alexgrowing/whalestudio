import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glBlock_finiteDim_module_structure : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act → ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → KStable act W → (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → (∀ U : Submodule ℂ V, U ≤ W → KStable act U → ∃ U' : Submodule ℂ V, KStable act U' ∧ U ⊓ U' = ⊥ ∧ U ⊔ U' = W) ∧ (W ≠ ⊥ → ∃ μ v, v ∈ W ∧ IsHW act μ v) ∧ (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, Submodule.span ℂ {w | w ∈ W ∧ OfType act μ w}) ∧ (∀ μ v, v ∈ W → IsHW act μ v → (∀ a b, posC a b → ∃ k : ℕ, μ a - μ b = k) ∧ OfType act μ v ∧ ∀ U : Submodule ℂ V, KStable act U → U ≤ sInf {N | v ∈ N ∧ KStable act N} → U = ⊥ ∨ v ∈ U) := by
  first | exact @GlobalTheory.BlockReps.finite_module_structure | exact GlobalTheory.BlockReps.finite_module_structure | (intros; apply GlobalTheory.BlockReps.finite_module_structure <;> assumption)

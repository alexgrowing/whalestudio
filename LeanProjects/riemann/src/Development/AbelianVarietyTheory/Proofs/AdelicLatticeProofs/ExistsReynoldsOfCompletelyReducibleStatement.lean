import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsReynoldsOfCompletelyReducible
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reynolds_of_completelyReducible' : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Set (V →ₗ[ℂ] V)), (∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, s v ∈ U) → ∃ U' : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U', s v ∈ U') ∧ IsCompl U U') → ∃ Rey : V →ₗ[ℂ] V, (∀ v, ∀ s ∈ S, s (Rey v) = Rey v) ∧ (∀ v, (∀ s ∈ S, s v = v) → Rey v = v) ∧ (∀ v, ∀ s ∈ S, Rey (s v) = Rey v) ∧ (∀ v, v - Rey v ∈ Submodule.span ℂ {x | ∃ s ∈ S, ∃ w, x = s w - w}) ∧ (∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v, Rey (T v) = T (Rey v)) ∧ ∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, s v ∈ U) → ∀ v ∈ U, Rey v ∈ U := by
  first | exact @GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible | exact GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible | (intros; apply GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible <;> assumption)

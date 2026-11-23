import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanGenEigenOfFiniteDimensionalOrbit
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_genEigen_of_finiteDimensional_orbit_alt : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)), (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → ∀ (X' : Set (Module.End ℂ V → ℂ)) (D : ℕ) (ψ : V), FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) → Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) ≤ D → (∀ (χ' : Module.End ℂ V → ℂ) (u : V), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) → u ≠ 0 → (∀ z ∈ A, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ A, χ' z = χ z) → ψ ∈ Submodule.span ℂ {ψ' | ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) ∧ ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D → (∀ z ∈ zs, z ∈ A) → zs.foldr (fun z f => z f - χ z • f) ψ' = 0} := by
  first | exact @GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit | exact GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit | (intros; apply GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit <;> assumption)

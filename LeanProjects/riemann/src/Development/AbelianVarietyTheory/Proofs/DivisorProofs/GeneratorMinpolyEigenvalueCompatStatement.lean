import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorMinpolyEigenvalueCompat
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_minpoly_eigenvalue_compat : ∀ (E : Type) [Field E] [NumberField E] (V : Type 1) [AddCommGroup V] [Module ℂ V] (P : E →+ V),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (b : E) (T : Module.End ℂ V), (∀ x, T (P x) = P (b * x)) →
    IntermediateField.adjoin ℚ {b} = ⊤ →
    Polynomial.aeval T ((minpoly ℚ b).map (algebraMap ℚ ℂ)) = 0 ∧
    ∀ (σ : E →+* ℂ) (a : E) (S : Module.End ℂ V), (∀ x, S (P x) = P (a * x)) → ∀ y, T y = σ b • y → S y = σ a • y := by
  first | exact @GlobalTheory.spanEquivariant_minpoly_eigen_transfer | exact GlobalTheory.spanEquivariant_minpoly_eigen_transfer | (intros; apply GlobalTheory.spanEquivariant_minpoly_eigen_transfer <;> assumption)

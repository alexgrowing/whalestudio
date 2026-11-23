import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerFixedFieldTraceEqSqMulOfAx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_fixedField_trace_eq_sq_mul_of_ax : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ) (J : Subgroup (L ≃ₐ[F] L)) [J.Normal] (σ₁ : L ≃ₐ[F] L) (c : ℤ), (p : L) ≠ 0 → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∀ σ ∈ J, (p : ℤ) ^ r ∣ a σ) → c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ → ∃ z : 𝒪[↥(IntermediateField.fixedField J)], Algebra.trace F ↥(IntermediateField.fixedField J) (z : ↥(IntermediateField.fixedField J)) = (p : F) ^ 2 * (c : F) := by
  first | exact @GlobalTheory.PMon.Ram.exists_integer_fixedField_trace_eq | exact GlobalTheory.PMon.Ram.exists_integer_fixedField_trace_eq | (intros; apply GlobalTheory.PMon.Ram.exists_integer_fixedField_trace_eq <;> assumption)

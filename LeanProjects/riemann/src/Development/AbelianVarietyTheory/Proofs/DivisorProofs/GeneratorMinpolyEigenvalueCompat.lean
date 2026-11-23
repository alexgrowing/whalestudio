import Mathlib

open Polynomial

namespace GlobalTheory

theorem spanEquivariant_aeval_map_apply {E : Type} [Field E] [NumberField E] {V : Type 1} [AddCommGroup V] [Module ℂ V]
    (P : E →+ V) (b : E) (T : Module.End ℂ V) (hT : ∀ x, T (P x) = P (b * x)) (q : ℚ[X]) :
    ∀ x, aeval T (q.map (algebraMap ℚ ℂ)) (P x) = P (aeval b q * x) := by
  induction q using Polynomial.induction_on with
  | C c =>
    intro x
    simp only [Polynomial.map_C, aeval_C, Module.algebraMap_end_apply]
    have h := map_ratCast_smul P E ℂ c x
    rw [smul_eq_mul] at h
    rw [eq_ratCast (algebraMap ℚ ℂ), eq_ratCast (algebraMap ℚ E), h]
  | add p q hp hq =>
    intro x
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hq, add_mul]
  | monomial n c ih =>
    intro x
    have e1 : (C c * X ^ (n + 1) : ℚ[X]) = (C c * X ^ n) * X := by ring
    rw [e1, Polynomial.map_mul, map_mul, Module.End.mul_apply, Polynomial.map_X, aeval_X, hT, ih,
      show aeval b (C c * X ^ n * X) = aeval b (C c * X ^ n) * b by rw [map_mul, aeval_X], mul_assoc]

theorem aeval_apply_of_apply_eq_smul {V : Type 1} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (μ : ℂ) (y : V)
    (hy : T y = μ • y) (q : ℂ[X]) : aeval T q y = q.eval μ • y := by
  induction q using Polynomial.induction_on with
  | C c => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n c ih =>
    have e1 : (C c * X ^ (n + 1) : ℂ[X]) = (C c * X ^ n) * X := by ring
    rw [e1, map_mul, Module.End.mul_apply, aeval_X, hy, map_smul, ih]
    conv_rhs => rw [eval_mul, eval_X]
    rw [smul_smul, mul_comm]

theorem spanEquivariant_minpoly_eigen_transfer : ∀ (E : Type) [Field E] [NumberField E] (V : Type 1) [AddCommGroup V] [Module ℂ V] (P : E →+ V),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (b : E) (T : Module.End ℂ V), (∀ x, T (P x) = P (b * x)) →
    IntermediateField.adjoin ℚ {b} = ⊤ →
    Polynomial.aeval T ((minpoly ℚ b).map (algebraMap ℚ ℂ)) = 0 ∧
    ∀ (σ : E →+* ℂ) (a : E) (S : Module.End ℂ V), (∀ x, S (P x) = P (a * x)) → ∀ y, T y = σ b • y → S y = σ a • y := by
  intro E _ _ V _ _ P hspan b T hT hadj
  constructor
  · apply LinearMap.ext_on_range hspan
    intro x
    rw [spanEquivariant_aeval_map_apply P b T hT, minpoly.aeval, zero_mul, map_zero, LinearMap.zero_apply]
  · intro σ a S hS y hy
    have hint : IsIntegral ℚ b := Algebra.IsIntegral.isIntegral b
    have ha : a ∈ Algebra.adjoin ℚ {b} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hadj]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨r, rfl⟩ := ha
    have hSeq : S = aeval T (r.map (algebraMap ℚ ℂ)) := by
      apply LinearMap.ext_on_range hspan
      intro x
      rw [hS, spanEquivariant_aeval_map_apply P b T hT]
      rfl
    rw [hSeq, aeval_apply_of_apply_eq_smul T (σ b) y hy, eval_map_algebraMap]
    congr 1
    exact Polynomial.aeval_algHom_apply σ.toRatAlgHom b r

end GlobalTheory

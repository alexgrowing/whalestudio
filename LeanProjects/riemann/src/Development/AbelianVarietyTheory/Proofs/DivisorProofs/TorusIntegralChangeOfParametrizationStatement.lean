import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusIntegralChangeOfParametrization
import Mathlib
open MeasureTheory Set
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_integral_change_of_parametrization : ∀ (ι X : Type) [Fintype ι] [TopologicalSpace X] [T2Space X] (e e' : (ι → ℝ) → X), Continuous e → Continuous e' → (∀ x y, e x = e y ↔ ∀ i, ∃ n : ℤ, x i - y i = n) → (∀ x y, e' x = e' y ↔ ∀ i, ∃ n : ℤ, x i - y i = n) → Set.range e = Set.range e' → (∀ x x' y y', e x = e' x' → e y = e' y' → e (x + y) = e' (x' + y')) → ∀ F : X → ℂ, ContinuousOn F (Set.range e) → ∫ x in Icc (0 : ι → ℝ) 1, F (e x) = ∫ x in Icc (0 : ι → ℝ) 1, F (e' x) := by
  first | exact @GlobalTheory.setIntegral_unitCube_eq_of_torus_parametrisations | exact GlobalTheory.setIntegral_unitCube_eq_of_torus_parametrisations | (intros; apply GlobalTheory.setIntegral_unitCube_eq_of_torus_parametrisations <;> assumption)

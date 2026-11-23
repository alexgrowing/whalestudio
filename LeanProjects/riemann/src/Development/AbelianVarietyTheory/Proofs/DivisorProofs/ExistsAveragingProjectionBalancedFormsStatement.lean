import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjectionBalancedForms
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_averaging_projection_balancedForms : ∀ (O : Type) [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] (n c : ℕ) (b : Fin n → O) (T : Matrix (Fin n) (Fin n) ℤ), 0 < c → (∀ s t, T s t = T t s) → (∀ (a : O) (g : O →ₗ[ℤ] O →ₗ[ℤ] ℤ), ∑ s, ∑ t, T s t * g (b s * a) (b t) = ∑ s, ∑ t, T s t * g (b s) (b t * bar a)) → ∑ s, ∑ t, T s t • (bar (b s) * b t) = (c : O) → (∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ s, ∑ t, T s t * v s * v t) → ∃ P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X, (∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → P β ∈ GlobalTheory.PolFan.balForms bar X) ∧ (∀ β ∈ GlobalTheory.PolFan.balForms bar X, P β = (c : ℤ) • β) ∧ ∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → P (GlobalTheory.PolFan.sqForm l) ≠ 0 ∧ ∀ x, 0 ≤ P (GlobalTheory.PolFan.sqForm l) x x := by
  first | exact @GlobalTheory.Poinc.exists_avg_proj_balForms | exact GlobalTheory.Poinc.exists_avg_proj_balForms | (intros; apply GlobalTheory.Poinc.exists_avg_proj_balForms <;> assumption)

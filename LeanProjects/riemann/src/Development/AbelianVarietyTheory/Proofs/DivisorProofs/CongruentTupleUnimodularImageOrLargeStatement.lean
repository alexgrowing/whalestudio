import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruentTupleUnimodularImageOrLarge
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruent_tuple_unimodular_image_or_large : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O), BddAct bar → ∀ (X₀ : Type) [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] [Module.Projective O X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (ι : Type) [Fintype ι] (a : ι → X₀), Submodule.span ℤ (Set.range a) = ⊤ → ∀ K : ℝ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X] (β : LinearMap.BilinForm ℤ X), β ∈ balForms bar X → (∀ y, 0 ≤ β y y) → ∀ lam : ℝ, 0 ≤ lam → (∀ x, x ≠ 0 → lam ≤ β x x) → ∀ (k : X₀ →ₗ[ℤ] X) (μ : ι → X), IsUnimodMod O N k → (∀ i, CongMod N (μ i) (k (a i))) → (∃ e : X₀ ≃ₗ[O] X, ∀ i, e (a i) = μ i) ∨ K * lam ≤ (∑ i, β (μ i) (μ i) : ℤ) := by
  first | exact @GlobalTheory.Poinc.dichotomy | exact GlobalTheory.Poinc.dichotomy | (intros; apply GlobalTheory.Poinc.dichotomy <;> assumption)

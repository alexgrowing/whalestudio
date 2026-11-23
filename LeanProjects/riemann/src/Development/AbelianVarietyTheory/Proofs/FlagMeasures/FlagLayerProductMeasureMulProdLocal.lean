import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem layerProd_eq_pow (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) :
    layerProd n f j τ id = layerProd n 1 j (fun i => τ i ^ f) id := by
  unfold layerProd
  simp only [id, mul_one]
  congr 1
  · refine prod_congr rfl fun i _ => prod_congr rfl fun k _ => ?_
    ring
  · refine prod_congr rfl fun i _ => ?_
    ring

noncomputable def layerHom (n : ℕ) {a : ℕ} (j : Fin a → ℕ) : (Fin a → ℝ) →* ℝ where
  toFun τ := layerProd n 1 j τ id
  map_one' := by simp [layerProd]
  map_mul' σ τ := by
    unfold layerProd
    simp only [id, Pi.mul_apply]
    rw [mul_mul_mul_comm]
    refine congrArg₂ (· * ·) ?_ ?_
    · rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun k _ => ?_
      rw [mul_div_mul_comm, mul_mul_mul_comm (σ i) (τ i), mul_pow (σ i / σ k), mul_pow (σ i * σ k)]
      ring
    · rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [mul_pow (σ i) (τ i) 2, mul_pow (σ i), mul_pow (σ i ^ 2)]
      ring

theorem layerProd_mul_prod : ∀ (ι : Type) [Fintype ι] (n f a : ℕ) (j : Fin a → ℕ) (s s₁ : Fin a → ℝ)
    (loc : ι → Fin a → ℝ), (∀ i, s i ^ f = s₁ i ^ f * ∏ v, loc v i) →
    layerProd n f j s id = layerProd n f j s₁ id * ∏ v, layerProd n 1 j (loc v) id := by
  intro ι _ n f a j s s₁ loc h

  have hs : (fun i => s i ^ f) = (fun i => s₁ i ^ f) * ∏ v, loc v := by
    funext i
    rw [h i, Pi.mul_apply, Finset.prod_apply]
  have key : ∀ τ : Fin a → ℝ, layerHom n j τ = layerProd n 1 j τ id := fun τ => rfl
  rw [layerProd_eq_pow, layerProd_eq_pow n f j s₁, ← key, ← key, hs, map_mul, map_prod]
  simp only [key]

end GlobalTheory.FlagMeas

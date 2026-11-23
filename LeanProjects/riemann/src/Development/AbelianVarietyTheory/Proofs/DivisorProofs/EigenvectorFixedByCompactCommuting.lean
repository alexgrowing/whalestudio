import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IncMatTransposeConjTranspose
open scoped TensorProduct Matrix
open NumberField Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl GlobalTheory.FockInclK

noncomputable section

namespace GlobalTheory.FockInclK

theorem exp_extMat_apply_of_ne {R S : ℕ} (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (Y : Mat R S)
    (b : Ix (R + 1) (S + 1)) (hb : ∀ c, b ≠ skipIx r₀ s₀ c) (a : Ix (R + 1) (S + 1)) :
    NormedSpace.exp (extMat r₀ s₀ Y) a b = if a = b then 1 else 0 := by
  let e : Matrix (Ix (R + 1) (S + 1)) (Fin 1) ℂ := Matrix.of fun a _ => if a = b then 1 else 0
  have h : extMat r₀ s₀ Y * e = e * (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext a' j
    simp [e, Matrix.mul_apply, extMat_apply, hb]
  have h2 := exp_mul_of_mul h
  rw [NormedSpace.exp_zero, Matrix.mul_one] at h2
  have h3 := congrFun (congrFun h2 a) 0
  simpa [e, Matrix.mul_apply] using h3

theorem mul_frame_eq_frame_mul_exp_extMat (d d₁ R S : ℕ) (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1))
    (K θ : Matrix (Fin d) (Fin d) ℂ)
    (K₁ : Matrix (Fin d₁) (Fin d₁) ℂ) (ιH : Matrix (Fin d) (Fin d₁) ℂ) (Cw : Matrix (Fin d) (Ix (R + 1) (S + 1)) ℂ)
    (C₁w : Matrix (Fin d₁) (Ix R S) ℂ) (Y : Mat R S) (x : Fin d → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hx : ∀ i, x i = c * (Cw i (.inl r₀) + Cw i (.inr s₀))) (hK : K *ᵥ x = x) (hθ : Commute K θ)
    (hJ : θ * Cw = Cw * Jm (R + 1) (S + 1)) (hC : ∀ i a, Cw i (skipIx r₀ s₀ a) = (ιH * C₁w) i a)
    (hι : K * ιH = ιH * K₁) (hY : C₁w * NormedSpace.exp Y = K₁ * C₁w) :
    K * Cw = Cw * NormedSpace.exp (extMat r₀ s₀ Y) := by
  set u : Fin d → ℂ := fun i => Cw i (.inl r₀) with hu
  set v : Fin d → ℂ := fun i => Cw i (.inr s₀) with hv
  have hx' : x = c • (u + v) := by
    funext i; simp [hx, hu, hv]
  have hsum : K *ᵥ (u + v) = u + v := by
    rw [hx', Matrix.mulVec_smul] at hK
    exact smul_right_injective _ hc hK
  have hθu : θ *ᵥ u = u := by
    funext i
    have := congrFun (congrFun hJ i) (.inl r₀)
    simp only [Matrix.mul_apply, Jm_apply] at this
    simpa [Matrix.mulVec, dotProduct, hu] using this
  have hθv : θ *ᵥ v = -v := by
    funext i
    have := congrFun (congrFun hJ i) (.inr s₀)
    simp only [Matrix.mul_apply, Jm_apply] at this
    simpa [Matrix.mulVec, dotProduct, hv] using this
  have hdiff : K *ᵥ (u - v) = u - v := by
    have e : θ *ᵥ (u + v) = u - v := by rw [Matrix.mulVec_add, hθu, hθv, sub_eq_add_neg]
    rw [← e, Matrix.mulVec_mulVec, hθ.eq, ← Matrix.mulVec_mulVec, hsum]
  rw [Matrix.mulVec_add] at hsum
  rw [Matrix.mulVec_sub] at hdiff
  have hKu : K *ᵥ u = u := by
    funext i
    have a1 := congrFun hsum i
    have a2 := congrFun hdiff i
    simp only [Pi.add_apply, Pi.sub_apply] at a1 a2
    linear_combination (a1 + a2) / 2
  have hKv : K *ᵥ v = v := by
    funext i
    have a1 := congrFun hsum i
    have a2 := congrFun hdiff i
    simp only [Pi.add_apply, Pi.sub_apply] at a1 a2
    linear_combination (a1 - a2) / 2
  have hCι : Cw * incMat r₀ s₀ = ιH * C₁w := by
    ext i a; rw [mul_incMat_apply, hC]
  have hskip : K * Cw * incMat r₀ s₀ = Cw * NormedSpace.exp (extMat r₀ s₀ Y) * incMat r₀ s₀ := by
    rw [Matrix.mul_assoc Cw, exp_mul_of_mul (extMat_mul_incMat r₀ s₀ Y), ← Matrix.mul_assoc Cw, hCι,
      Matrix.mul_assoc K, hCι, ← Matrix.mul_assoc K, hι, Matrix.mul_assoc, Matrix.mul_assoc, hY]
  have hfix : ∀ b, (∀ c, b ≠ skipIx r₀ s₀ c) → ∀ i, (Cw * NormedSpace.exp (extMat r₀ s₀ Y)) i b = Cw i b := by
    intro b hb i
    simp [Matrix.mul_apply, exp_extMat_apply_of_ne r₀ s₀ Y b hb]
  ext i b
  by_cases hb : ∃ c, b = skipIx r₀ s₀ c
  · obtain ⟨a, rfl⟩ := hb
    have := congrFun (congrFun hskip i) a
    rwa [mul_incMat_apply, mul_incMat_apply] at this
  · push Not at hb
    rw [hfix b hb]
    rcases b with r | s
    · obtain rfl : r = r₀ := by
        by_contra h
        obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq h
        exact hb (.inl a) (by simp [skipIx, ha])
      exact congrFun hKu i
    · obtain rfl : s = s₀ := by
        by_contra h
        obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq h
        exact hb (.inr a) (by simp [skipIx, ha])
      exact congrFun hKv i

end GlobalTheory.FockInclK

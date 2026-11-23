import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem inv_form_of_rel {S : Type*} [Ring S] [Algebra ℚ S] (b b' y : Sˣ) (z : S) (s : ℚ)
    (h : (b' : S) = algebraMap ℚ S s * (y * b * z)) :
    s • (z * ((b'⁻¹ : Sˣ) : S) * y) = ((b⁻¹ : Sˣ) : S) := by
  have h1 : algebraMap ℚ S s * (y * b * z) * ((b'⁻¹ : Sˣ) : S) = 1 := by rw [← h, Units.mul_inv]
  calc s • (z * ((b'⁻¹ : Sˣ) : S) * y)
      = ((b⁻¹ : Sˣ) : S) * ((y⁻¹ : Sˣ) : S) * (algebraMap ℚ S s * (y * b * z) * ((b'⁻¹ : Sˣ) : S)) * y := by
        simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc, Units.inv_mul_cancel_left]
    _ = _ := by rw [h1, mul_one, mul_assoc, Units.inv_mul, mul_one]

theorem form_of_rel {p : ℕ} [Fact p.Prime] {G : HTGroup p} (b b' y : G.Cˣ) (s : ℚ)
    (h : (b' : G.C) = algebraMap ℚ G.C s * (y * b * sh G y)) (v : InfinitePlace G.F) (x : Fin G.n → ℂ) :
    (star x ⬝ᵥ ((G.gram v * G.psi v ((b⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re =
      (s : ℝ) * (star (G.psi v y *ᵥ x) ⬝ᵥ
        ((G.gram v * G.psi v ((b'⁻¹ : G.Cˣ) : G.C)) *ᵥ (G.psi v y *ᵥ x))).re := by
  have hu : IsUnit (G.gram v).det := (G.gram_det v).isUnit
  have e : G.gram v * G.psi v ((b⁻¹ : G.Cˣ) : G.C) =
      (s : ℂ) • ((G.psi v y)ᴴ * (G.gram v * G.psi v ((b'⁻¹ : G.Cˣ) : G.C)) * G.psi v y) := by
    rw [← inv_form_of_rel b b' y _ s h, map_rat_smul, map_mul, map_mul, sh, G.psi_star, Matrix.mul_smul,
      ← Rat.cast_smul_eq_qsmul ℂ]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  rw [e, Matrix.smul_mulVec, dotProduct_smul, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, smul_eq_mul, ← Complex.ofReal_ratCast, Complex.re_ofReal_mul]

theorem mark_iff_of_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (μ : ℂ),
    P.Rel Q → (P.Mark μ ↔ Q.Mark μ) := by
  rintro p _ G P Q μ ⟨y, s, hs, hβ, hγ⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · rintro ⟨v, hv, x, hx, hpos⟩
    refine ⟨v, hv, G.psi v y *ᵥ x, ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← map_mul, hγ, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, map_mul,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    · rw [form_of_rel P.β Q.β y s hβ] at hpos
      exact (mul_pos_iff_of_pos_left hs').1 hpos
  · rintro ⟨v, hv, x, hx, hpos⟩
    refine ⟨v, hv, G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x, ?_, ?_⟩
    · have e : P.γ * y⁻¹ = y⁻¹ * Q.γ := by rw [hγ]; group
      rw [Matrix.mulVec_mulVec, ← map_mul, ← Units.val_mul, e, Units.val_mul, map_mul,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    · rw [form_of_rel P.β Q.β y s hβ, Matrix.mulVec_mulVec x (G.psi v y), ← map_mul, Units.mul_inv, map_one,
        Matrix.one_mulVec]
      exact mul_pos hs' hpos

end GlobalTheory.LKMid.Pair

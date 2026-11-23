import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.DFormPos

theorem sim_pos : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) (y : G.Cˣ) (s : ℚ),
    (y : G.C) * B.β * sh G y = algebraMap ℚ G.C s * B.β → 0 < s := by
  intro p _ G B y s hsim0
  obtain ⟨v⟩ : Nonempty (InfinitePlace G.F) := inferInstance
  set h := G.gram v
  set A := G.psi v (y : G.C)
  set Ai := G.psi v ((y⁻¹ : G.Cˣ) : G.C)
  set Pb := G.psi v (B.β : G.C)
  set Bm := G.psi v ((B.β⁻¹ : G.Cˣ) : G.C)
  set c : ℂ := ((s : ℚ) : ℂ)
  have hsim := congrArg (G.psi v) hsim0
  have hc : G.psi v (algebraMap ℚ G.C s) = c • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F]
    ext i j; simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, c]
  rw [map_mul, map_mul, map_mul, hc] at hsim
  change A * Pb * G.psi v (G.star (y : G.C)).unop = _ at hsim
  rw [G.psi_star, Matrix.smul_mul, Matrix.one_mul] at hsim
  have hBβ : Bm * Pb = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hβB : Pb * Bm = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hAiA : Ai * A = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hdet : IsUnit h.det := isUnit_iff_ne_zero.2 (G.gram_det v)
  have hhi : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h hdet
  have e1 : Aᴴ * h = c • (h * Bm * Ai * Pb) := by
    have := congrArg (fun M => h * Bm * Ai * M) hsim
    calc Aᴴ * h = h * Bm * Ai * (A * Pb * (h⁻¹ * Aᴴ * h)) := by
          simp only [← Matrix.mul_assoc]
          rw [Matrix.mul_assoc (h * Bm) Ai A, hAiA, Matrix.mul_one, Matrix.mul_assoc h Bm Pb, hBβ, Matrix.mul_one, hhi,
            Matrix.one_mul]
      _ = _ := by rw [this, Matrix.mul_smul]
  have key : Aᴴ * (h * Bm) * A = c • (h * Bm) := by
    rw [← Matrix.mul_assoc, e1, Matrix.smul_mul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pb Bm A, hβB, Matrix.one_mul, hAiA, Matrix.mul_one]
  obtain ⟨x, hx⟩ : ∃ x : Fin G.n → ℂ, x ≠ 0 := ⟨Pi.single ⟨0, G.n_pos⟩ 1, by simp⟩
  have hAx : A *ᵥ x ≠ 0 := fun h0 => hx (by
    have := congrArg (Ai *ᵥ ·) h0
    simpa [Matrix.mulVec_mulVec, hAiA] using this)
  have e2 : star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x)) = c * (star x ⬝ᵥ ((h * Bm) *ᵥ x)) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc] at key ⊢
    rw [key, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hcr : c = ((s : ℝ) : ℂ) := by simp [c]
  have h1 := B.posR v x hx
  have h2 := B.posR v _ hAx
  change (_ → 0 < (star x ⬝ᵥ ((h * Bm) *ᵥ x)).re) ∧ (_ → (star x ⬝ᵥ ((h * Bm) *ᵥ x)).re < 0) at h1
  change (_ → 0 < (star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x))).re) ∧
    (_ → (star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x))).re < 0) at h2
  rw [e2, hcr, Complex.re_ofReal_mul] at h2
  have hs : (0 : ℝ) < s := by
    by_cases hv : sigPosH (G.gram_herm v) = 1
    · have a1 := h1.1 hv
      have a2 := h2.1 hv
      by_contra hn
      push_neg at hn
      nlinarith
    · have a1 := h1.2 hv
      have a2 := h2.2 hv
      by_contra hn
      push_neg at hn
      nlinarith
  exact_mod_cast hs

end GlobalTheory.LKDef.DFormPos

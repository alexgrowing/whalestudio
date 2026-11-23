import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacter
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem pos_iff_smul_toV (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (g : grp G β)
    (z : Fin G.n → ℂ) (c : ℂ) : c ≠ 0 →
    (0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ↔ 0 < (star (c • ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) ⬝ᵥ
      (herm G v β *ᵥ (c • ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)))).re) := by
  intro hc
  set M : Matrix (Fin G.n) (Fin G.n) ℂ := (toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) with hM
  set H := herm G v β
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G v β g
  have hs : (0 : ℚ) < (((g : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := g.2.2
  set s : ℚ := (((g : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)
  have key : star (c • (M *ᵥ z)) ⬝ᵥ (H *ᵥ (c • (M *ᵥ z))) =
      ((Complex.normSq c * s : ℝ) : ℂ) * (star z ⬝ᵥ (H *ᵥ z)) := by
    have e1 : star (M *ᵥ z) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star z ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, e1, hsim, Matrix.smul_mulVec,
      dotProduct_smul]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    simp [mul_comm]
  rw [key, Complex.re_ofReal_mul]
  have hpos : 0 < Complex.normSq c * (s : ℝ) :=
    mul_pos (Complex.normSq_pos.2 hc) (by exact_mod_cast hs)
  exact (mul_pos_iff_of_pos_left hpos).symm

end GlobalTheory.LKCx

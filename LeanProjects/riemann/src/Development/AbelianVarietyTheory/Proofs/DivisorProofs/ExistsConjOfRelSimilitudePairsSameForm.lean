import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ConjR

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul' (G : HTGroup p) (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_unit_mul_inv (G : HTGroup p) (y : G.Cˣ) : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul', Units.inv_mul]; simp [sh]

theorem conj_of_rel (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G) (B y y' : G.Cˣ) (s s' : ℚ)
    (hs : 0 < s) (hs' : 0 < s')
    (hP : (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y))
    (hP' : (P'.β : G.C) = algebraMap ℚ G.C s' * (y' * B * sh G y')) (hR : P.Rel P') :
    ∃ (g : G.Cˣ) (sg : ℚ), 0 < sg ∧ (g : G.C) * B * sh G g = algebraMap ℚ G.C sg * B ∧
      g * (y⁻¹ * P.γ * y) * g⁻¹ = y'⁻¹ * P'.γ * y' := by
  obtain ⟨z, sr, hsr, hβ, hγ⟩ := hR
  refine ⟨y'⁻¹ * z * y, s' / (s * sr), div_pos hs' (mul_pos hs hsr), ?_, ?_⟩
  · rw [← Algebra.smul_def] at hP hP' hβ ⊢
    set a : G.Cˣ := y'⁻¹
    have E : s' • ((y' : G.C) * B * sh G y') = (sr * s) • ((z : G.C) * (y * B * sh G y) * sh G z) := by
      rw [← hP', hβ, hP, mul_smul, mul_smul_comm, smul_mul_assoc]
    have E2 := congrArg (fun X => (a : G.C) * X * sh G a) E
    have ha1 : (a : G.C) * y' = 1 := Units.inv_mul y'
    have ha2 : sh G (y' : G.C) * sh G a = 1 := sh_unit_mul_inv G y'
    have L : (a : G.C) * (s' • ((y' : G.C) * B * sh G y')) * sh G a = s' • (B : G.C) := by
      rw [mul_smul_comm, smul_mul_assoc]
      congr 1
      calc (a : G.C) * ((y' : G.C) * B * sh G y') * sh G a = ((a : G.C) * y') * B * (sh G y' * sh G a) := by
            simp only [mul_assoc]
        _ = _ := by rw [ha1, ha2, one_mul, mul_one]
    have R : (a : G.C) * ((sr * s) • ((z : G.C) * (y * B * sh G y) * sh G z)) * sh G a =
        (sr * s) • (((a * z * y : G.Cˣ) : G.C) * B * sh G ((a * z * y : G.Cˣ) : G.C)) := by
      rw [mul_smul_comm, smul_mul_assoc]
      congr 1
      simp only [Units.val_mul, sh_mul', mul_assoc]
    rw [L, R] at E2
    have hne : (sr * s) ≠ 0 := (mul_pos hsr hs).ne'
    rw [show s' / (s * sr) = (sr * s)⁻¹ * s' by rw [div_eq_inv_mul, mul_comm s sr], mul_smul, E2, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  · rw [hγ]; group

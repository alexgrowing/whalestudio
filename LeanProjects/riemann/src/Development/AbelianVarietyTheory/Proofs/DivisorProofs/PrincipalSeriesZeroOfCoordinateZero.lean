import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD

noncomputable section

open Matrix

namespace GlobalTheory.PrinTwo

theorem eq_zero_of_ev_one_of_coord {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : PSp μ₁ μ₂) (h1 : ev f 1 = 0)
    (hc : ∀ x : k, coord f x = 0) : f = 0 := by
  apply ext_ev
  intro g
  have hz : ev (0 : PSp μ₁ μ₂) g = 0 := by
    have := ev_smul (0 : ℂ) (0 : PSp μ₁ μ₂) g
    simpa using this
  rw [hz]
  have hdet : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit |>.ne_zero
  rw [Matrix.det_fin_two] at hdet
  by_cases hr : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 = 0
  · rw [hr, mul_zero, sub_zero] at hdet
    have hp : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
    have hs : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
    have hg : g = bor (Units.mk0 _ hp) (Units.mk0 _ hs) ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 1) * 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hr]
    rw [hg, ev_bor, h1, mul_zero]
  · set D := (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0 * (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 -
      (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 1 * (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 with hD
    have hA : -D / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 ≠ 0 := div_ne_zero (neg_ne_zero.2 hdet) hr
    have hg : g = bor (Units.mk0 _ hA) (Units.mk0 _ hr) ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0) *
        (wE * nU ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0)) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hD] <;> field_simp <;> ring
    rw [hg, ev_bor]
    have := hc ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0)
    rw [coord] at this
    rw [this, mul_zero]

end GlobalTheory.PrinTwo

import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial MeasureTheory

namespace GlobalTheory.SchurPol

theorem polarise_integral {G H : Type*} [MeasurableSpace G] [AddCommGroup H] [Module ℂ H]
    (μ : Measure G) (F : H → H → G → ℂ) (R : H → H → ℂ) (c : ℂ)
    (hF : ∀ x y g, F x y g = (1 / 4 : ℂ) * ((F (x + y) (x + y) g - F (x - y) (x - y) g) +
      c * (F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g)))
    (hR : ∀ x y, R x y = (1 / 4 : ℂ) * ((R (x + y) (x + y) - R (x - y) (x - y)) +
      c * (R (x + Complex.I • y) (x + Complex.I • y) -
        R (x - Complex.I • y) (x - Complex.I • y))))
    (hd : ∀ x, Integrable (F x x) μ ∧ ∫ g, F x x g ∂μ = R x x) (x y : H) :
    Integrable (F x y) μ ∧ ∫ g, F x y g ∂μ = R x y := by
  have e : F x y = fun g => (1 / 4 : ℂ) * ((F (x + y) (x + y) g - F (x - y) (x - y) g) +
      c * (F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g)) := funext (hF x y)
  have h1 : Integrable (fun g => F (x + y) (x + y) g - F (x - y) (x - y) g) μ :=
    (hd _).1.sub (hd _).1
  have h2 : Integrable (fun g => F (x + Complex.I • y) (x + Complex.I • y) g -
        F (x - Complex.I • y) (x - Complex.I • y) g) μ := (hd _).1.sub (hd _).1
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (h1.add (h2.const_mul c)).const_mul _
  · rw [hR x y]
    simp only [hF x y]
    rw [integral_const_mul, integral_add h1 (h2.const_mul c), integral_const_mul,
      integral_sub (hd _).1 (hd _).1, integral_sub (hd _).1 (hd _).1,
      (hd _).2, (hd _).2, (hd _).2, (hd _).2]

theorem schur_half {p q : ℕ} {T : GrpData p q} (D : DSRep T) (w u₁ u₂ : D.U.H) :
    Integrable (fun g => inner ℂ w (D.U.π g u₁) * star (inner ℂ w (D.U.π g u₂))) T.haar ∧
      ∫ g, inner ℂ w (D.U.π g u₁) * star (inner ℂ w (D.U.π g u₂)) ∂T.haar =
        ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ w w) := by
  refine polarise_integral T.haar
    (fun x y g => inner ℂ w (D.U.π g x) * star (inner ℂ w (D.U.π g y)))
    (fun x y => ((D.fdeg : ℂ))⁻¹ * inner ℂ y x * star (inner ℂ w w)) Complex.I ?_ ?_ ?_ u₁ u₂
  · intro x y g
    simp only [map_add, map_sub, map_smul, inner_add_right, inner_sub_right, inner_smul_right,
      star_add, star_sub, star_mul', Complex.star_def, Complex.conj_I]
    linear_combination (1 / 2 : ℂ) * (inner ℂ w (D.U.π g x) * (starRingEnd ℂ) (inner ℂ w (D.U.π g y))
      - inner ℂ w (D.U.π g y) * (starRingEnd ℂ) (inner ℂ w (D.U.π g x))) * Complex.I_mul_I
  · intro x y
    simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_add_left, inner_sub_left,
      inner_smul_left, Complex.conj_I]
    linear_combination (1 / 2 : ℂ) * ((D.fdeg : ℂ))⁻¹ * star (inner ℂ w w) *
      (inner ℂ y x - inner ℂ x y) * Complex.I_mul_I
  · intro x
    have e : ∀ g, inner ℂ w (D.U.π g x) * star (inner ℂ w (D.U.π g x)) =
        ((‖inner ℂ w (D.U.π g x)‖ ^ 2 : ℝ) : ℂ) := by
      intro g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e]
    refine ⟨(D.schur x w).1.ofReal, ?_⟩
    rw [integral_complex_ofReal, (D.schur x w).2, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K]
    simp only [Complex.star_def, map_pow, Complex.coe_algebraMap, Complex.conj_ofReal]
    push_cast
    ring

theorem schur_polarised (p q : ℕ) (T : GrpData p q) (D : DSRep T) (u₁ w₁ u₂ w₂ : D.U.H) :
    Integrable (fun g => inner ℂ w₁ (D.U.π g u₁) * star (inner ℂ w₂ (D.U.π g u₂))) T.haar ∧
      ∫ g, inner ℂ w₁ (D.U.π g u₁) * star (inner ℂ w₂ (D.U.π g u₂)) ∂T.haar =
        ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ w₂ w₁) := by
  refine polarise_integral T.haar
    (fun x y g => inner ℂ x (D.U.π g u₁) * star (inner ℂ y (D.U.π g u₂)))
    (fun x y => ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ * star (inner ℂ y x)) (-Complex.I) ?_ ?_
    (fun x => schur_half D x u₁ u₂) w₁ w₂
  · intro x y g
    simp only [inner_add_left, inner_sub_left, inner_smul_left, map_add, map_sub, map_mul, map_neg,
      star_add, star_sub, star_mul', Complex.star_def, Complex.conj_I, neg_neg]
    linear_combination (1 / 2 : ℂ) *
      (inner ℂ x (D.U.π g u₁) * (starRingEnd ℂ) (inner ℂ y (D.U.π g u₂))
      - inner ℂ y (D.U.π g u₁) * (starRingEnd ℂ) (inner ℂ x (D.U.π g u₂))) * Complex.I_mul_I
  · intro x y
    simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_add_left, inner_sub_left,
      inner_smul_left, Complex.conj_I, Complex.star_def, map_add, map_sub, map_mul, map_neg,
      neg_neg]
    linear_combination (1 / 2 : ℂ) * ((D.fdeg : ℂ))⁻¹ * inner ℂ u₂ u₁ *
      ((starRingEnd ℂ) (inner ℂ y x) - (starRingEnd ℂ) (inner ℂ x y)) * Complex.I_mul_I

end GlobalTheory.SchurPol

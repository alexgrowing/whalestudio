import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv

open UpperTheory.V.Sd.Eis

private theorem complex_linear_combination_eq_half_of_relations (a b c d e f x y z w κ : ℂ) (hc : c - Complex.I * d ≠ 0)
    (h1 : a * e + b * f = 1) (h2 : c * e + d * f = 0)
    (hp1 : x + w = 0) (hp2 : y - z = Complex.I * κ) (hp3 : x - w = Complex.I * (y + z))
    (hE : e * (c * x + d * y) + f * (c * z + d * w) = 0) :
    e * (a * x + b * y) + f * (a * z + b * w) = κ / 2 := by
  have hw : w = -x := by linear_combination hp1
  have hs : y + z = -2 * Complex.I * x := by
    linear_combination (norm := skip) (Complex.I) * hp3 + (Complex.I) * hp1
    ring_nf; simp only [Complex.I_sq]; ring_nf
  have hy : y = -Complex.I * x + Complex.I * κ / 2 := by
    linear_combination (1/2) * hs + (1/2) * hp2
  have hz : z = -Complex.I * x - Complex.I * κ / 2 := by
    linear_combination (1/2) * hs - (1/2) * hp2
  subst hw hy hz
  apply mul_left_cancel₀ hc
  linear_combination (norm := skip) (a - Complex.I * b) * hE
    + (-κ/2) * (Complex.I * d - c) * h1 + (-κ/2) * (a - Complex.I * b) * h2
  ring_nf; simp only [Complex.I_sq, Complex.I_pow_four]; ring_nf

theorem UpperTheory.eisenstein_lie_algebra_action :
    UpperTheory.V.Sd.Eis.LieAlg := by
  intro h p κ hp1 hp2 hp3 hE
  have hMN : (h : Matrix (Fin 2) (Fin 2) ℝ) * ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1 := congrFun (congrFun hMN 0) 0
  have e2 := congrFun (congrFun hMN 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e1 e2
  have hdet : (h : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hMN
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [Matrix.det_fin_two] at hdet
  have hc : ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) - Complex.I * ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp at hre him
    apply hdet
    rw [hre, him]; ring
  have hent : ∀ (k i j : Fin 2),
      (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.single (0 : Fin 2) k (1 : ℝ)
        * (h : Matrix (Fin 2) (Fin 2) ℝ)) i j
        = ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) k j := by
    intro k i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  simp only [hent, Fin.sum_univ_two, Complex.ofReal_mul] at hE ⊢
  have e1' : ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)
      + ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 1 := by
    exact_mod_cast e1
  have e2' : ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)
      + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 0 := by
    exact_mod_cast e2
  have := complex_linear_combination_eq_half_of_relations _ _ _ _ _ _ (p 0 0) (p 0 1) (p 1 0) (p 1 1) κ hc e1' e2' hp1 hp2 hp3
    (by linear_combination hE)
  linear_combination this

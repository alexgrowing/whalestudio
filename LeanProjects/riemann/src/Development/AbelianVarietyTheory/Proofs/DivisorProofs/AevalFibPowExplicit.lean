import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HPolyAddTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompFsDens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivFractionsBilinearFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEvalHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAffinePowEqHPoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableProdQCoefMulFsDens

set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine

theorem eval_fibPow (H : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    MvPolynomial.eval (entries H) (fibPow k) = ∫ x : ℂ, qMat H x ^ k * (fsDens x : ℂ) := by
  have e : ∀ x : ℂ, qMat H x ^ k * (fsDens x : ℂ) =
      ∑ f : Fin k → Fin 2 × Fin 2, (∏ i, qCoef x (f i)) * (fsDens x : ℂ) * ∏ i, entries H (f i) := by
    intro x
    rw [qMat, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [smul_eq_mul, Finset.prod_mul_distrib]
    ring
  simp only [fibPow, map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  simp_rw [e]
  rw [integral_finset_sum _ fun f _ => ((Intg.integrable_prod_qCoef_mul_fsDens k f).mul_const _)]
  simp only [integral_mul_const]

theorem qMat_diagonal (a b x : ℂ) : qMat (Matrix.diagonal ![a, b]) x =
    ((1 / (1 + ‖x‖ ^ 2) : ℝ) : ℂ) * a + (1 - ((1 / (1 + ‖x‖ ^ 2) : ℝ) : ℂ)) * b := by
  have h0 : (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hx : x * starRingEnd ℂ x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [qMat, entries, Fintype.sum_prod_type, Fin.sum_univ_two, qCoef, lineVec, Matrix.diagonal_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, if_true, if_false, smul_zero, add_zero,
    zero_add, smul_eq_mul, map_one, mul_one, hx]
  simp
  left
  have h1 : (1 + (‖x‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h0
  field_simp
  ring

theorem fibPow_diagonal (a b : ℂ) (k : ℕ) : MvPolynomial.eval (entries (Matrix.diagonal ![a, b])) (fibPow k) =
    ∫ t in (0 : ℝ)..1, ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k := by
  rw [eval_fibPow]
  simp_rw [qMat_diagonal]
  exact integral_comp_fsDens (fun t : ℝ => ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k) (by fun_prop)

theorem eval_trDet {R : Type} [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (p : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.aeval (entries H) (MvPolynomial.aeval trDet p) = MvPolynomial.aeval ![H.trace, H.det] p := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have e : (fun i => MvPolynomial.aeval (entries H) (trDet i)) = ![H.trace, H.det] := by
    funext i
    fin_cases i <;> simp [trDet, entries, Matrix.trace_fin_two, Matrix.det_fin_two]
  rw [e]

theorem fibPow_eq (k : ℕ) : fibPow k = (1 / ((k : ℂ) + 1)) • MvPolynomial.aeval trDet (hPoly k) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_eval_hermitian _ fun H hH => ?_
  have hR : MvPolynomial.eval (entries H) (MvPolynomial.aeval trDet (hPoly k)) =
      MvPolynomial.eval ![H.trace, H.det] (hPoly k) := by
    simpa [MvPolynomial.coe_aeval_eq_eval] using eval_trDet H (hPoly k)
  rw [map_sub, sub_eq_zero, MvPolynomial.smul_eval, hR, eval_fibPow]
  set l₀ := (hH.eigenvalues 0 : ℂ)
  set l₁ := (hH.eigenvalues 1 : ℂ)
  have hD : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) = Matrix.diagonal ![l₀, l₁] := by
    congr 1; funext i; fin_cases i <;> rfl
  have hs := hH.spectral_theorem
  rw [hD, Unitary.conjStarAlgAut_apply] at hs
  have htr : H.trace = l₀ + l₁ := by rw [hH.trace_eq_sum_eigenvalues, Fin.sum_univ_two]; rfl
  have hdet : H.det = l₀ * l₁ := by rw [hH.det_eq_prod_eigenvalues, Fin.prod_univ_two]; rfl
  rw [htr, hdet]
  conv_lhs => rw [hs]
  rw [UnitaryInv.integral_qMat_unitary_conj _ (hH.eigenvectorUnitary).2, ← eval_fibPow, fibPow_diagonal, integral_affine_pow_eq_hPoly]
  ring

theorem eq_zero_of_eval_symm (P : MvPolynomial (Fin 2) ℂ) (h : ∀ a b : ℂ, MvPolynomial.eval ![a + b, a * b] P = 0) :
    P = 0 := by
  refine MvPolynomial.funext fun y => ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y 0 ^ 2 - 4 * y 1) two_pos
  have e : ![(y 0 + z) / 2 + (y 0 - z) / 2, (y 0 + z) / 2 * ((y 0 - z) / 2)] = y := by
    funext i
    fin_cases i
    · simp; ring
    · simp; linear_combination (-1 / 4 : ℂ) * hz
  simpa [e] using h ((y 0 + z) / 2) ((y 0 - z) / 2)

theorem aeval_fibPow {R : Type} [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    MvPolynomial.aeval (entries H) (fibPow k) =
      (1 / ((k : ℂ) + 1)) • MvPolynomial.aeval ![H.trace, H.det] (hPoly k) := by
  rw [fibPow_eq, map_smul, eval_trDet]

theorem aeval_fibPow_explicit : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (k : ℕ),
    MvPolynomial.aeval (entries H) (fibPow k) =
      (1 / ((k : ℂ) + 1)) • MvPolynomial.aeval ![H.trace, H.det] (hPoly k) :=
  fun _ _ _ H k => aeval_fibPow H k

end GlobalTheory.FibLine

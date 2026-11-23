import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.FlagPsLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open Polynomial Matrix

noncomputable section

variable {N : ℕ} (p i : ℕ) (hi : i ≤ N)

theorem lowerMatrix_strict (u : LowerPair N → ℂ) :
    ∀ a b : Fin N, ¬ b < a → lowerMatrix u a b = 0 := by
  intro a b h
  simp [lowerMatrix, h]

theorem coeff_trace_kerPoly (L : Matrix (Fin N) (Fin N) ℂ) :
    (kerPoly p i hi L).trace.coeff 0 = (sigTop p i hi * tailForm p i hi L).trace := by
  have hV : (topPoly i hi L).map (evalRingHom 0) = 1 := by
    refine Matrix.ext fun a b => ?_
    simp [topPoly, colPoly, Matrix.one_apply, Fin.castLE_inj] <;> split_ifs <;> simp
  have hV' : (topPoly' i hi L).map (evalRingHom 0) = 1 := by
    refine Matrix.ext fun a b => ?_
    simp [topPoly', rowPoly, Matrix.one_apply, Fin.castLE_inj, eq_comm] <;> split_ifs <;> simp
  have hadj : ∀ M : Matrix (Fin i) (Fin i) ℂ[X],
      M.adjugate.map (evalRingHom 0) = (M.map (evalRingHom 0)).adjugate := fun M =>
    (evalRingHom (0 : ℂ)).map_adjugate M
  have hC : ∀ M : Matrix (Fin i) (Fin i) ℂ, (M.map C).map (evalRingHom 0) = M := fun M => by
    refine Matrix.ext fun a b => ?_
    simp
  have hmap : (kerPoly p i hi L).map (evalRingHom 0) = sigTop p i hi * tailForm p i hi L := by
    simp only [kerPoly, Matrix.map_mul, hadj, hV, hV', adjugate_one, Matrix.mul_one, hC]
  rw [coeff_zero_eq_eval_zero, ← hmap]
  simp [Matrix.trace, eval_finsetSum]

theorem re_trace_sigTop_tail (L : Matrix (Fin N) (Fin N) ℂ) :
    (sigTop p i hi * tailForm p i hi L).trace.re = tailSum p i L := by
  rw [tailSum, sum_fin_split_castLE hi (fun b => ∑ c : Fin N,
    if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0)]
  have h2 : (∑ b : Fin N, if i ≤ b.val then (∑ c : Fin N,
      if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0) else 0) =
      0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · exact Finset.sum_eq_zero fun c _ => if_neg (by omega)
    · rfl
  rw [h2, add_zero, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.diag_apply, sigTop, tailForm, Matrix.diagonal_mul, Matrix.of_apply,
    Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have ha : (Fin.castLE hi a).val < i := by simp
  by_cases hc : i ≤ c.val
  · rw [if_pos hc, if_pos ⟨ha, hc⟩]
    have : star (L c (Fin.castLE hi a)) * ((sigSign p c : ℝ) : ℂ) * L c (Fin.castLE hi a) =
        ((sigSign p c * ‖L c (Fin.castLE hi a)‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm (star _), mul_assoc, Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  · rw [if_neg hc, if_neg (fun h => hc h.2)]
    simp

theorem colPoly_eval (u : LowerPair N → ℂ) (t : ℝ) :
    (colPoly i hi (lowerMatrix u)).map (evalRingHom (t : ℂ)) =
      ((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id (Fin.castLE hi) := by
  refine Matrix.ext fun c b => ?_
  by_cases h : Fin.castLE hi b < c
  · simp [colPoly, lowerMatrix, Matrix.one_apply, h, Complex.real_smul] <;> split_ifs <;>
      simp [mul_comm]
  · simp [colPoly, lowerMatrix, Matrix.one_apply, h] <;> split_ifs <;> simp

theorem rowPoly_eval (u : LowerPair N → ℂ) (t : ℝ) :
    (rowPoly i hi (lowerMatrix u)).map (evalRingHom (t : ℂ)) =
      (((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id
        (Fin.castLE hi)).conjTranspose := by
  refine Matrix.ext fun a c => ?_
  by_cases h : Fin.castLE hi a < c
  · have h2 : c ≠ Fin.castLE hi a := fun h' => by rw [h'] at h; exact lt_irrefl _ h
    simp only [Matrix.map_apply, rowPoly, Matrix.of_apply, coe_evalRingHom, eval_add, eval_mul,
      eval_X, eval_C, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq,
      Matrix.add_apply, Matrix.one_apply, lowerMatrix, dif_pos h, if_neg h2, eval_zero, zero_add]
    simp [Complex.real_smul, mul_comm]
  · by_cases h2 : c = Fin.castLE hi a
    · subst h2; simp [rowPoly, lowerMatrix]
    · simp [rowPoly, lowerMatrix, h, h2]

theorem det_flag_eval (u : LowerPair N → ℂ) (t : ℝ) :
    ((((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id
        (Fin.castLE hi)).conjTranspose * signatureForm N p *
        ((1 + lowerMatrix (t • u)).submatrix id (Fin.castLE hi))).det =
      (sigTop p i hi).det *
        ((1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi (lowerMatrix u)).det).eval (t : ℂ) := by
  have hS : signatureForm N p = ((signatureForm N p).map C).map (evalRingHom (t : ℂ)) := by
    refine Matrix.ext fun a b => ?_
    simp
  rw [← rowPoly_eval, ← colPoly_eval, hS, ← Matrix.map_mul, ← Matrix.map_mul]
  rw [show ∀ M : Matrix (Fin i) (Fin i) ℂ[X], (M.map (evalRingHom (t : ℂ))).det =
      evalRingHom (t : ℂ) M.det from fun M => ((evalRingHom (t : ℂ)).map_det M).symm]
  rw [det_gram p i hi (lowerMatrix_strict u)]
  simp

theorem norm_det_sigTop : ‖(sigTop p i hi).det‖ = 1 := by
  rw [sigTop, det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sigSign
  split_ifs <;> simp

theorem flagPs_smul (u : LowerPair N → ℂ) (t : ℝ) :
    flagPs N p i hi (t • u) =
      Real.log ‖((1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi (lowerMatrix u)).det).eval (t : ℂ)‖ := by
  rw [flagPs, det_flag_eval, norm_mul, norm_det_sigTop, one_mul]

theorem deriv_deriv_flagPs (u : LowerPair N → ℂ) :
    deriv (deriv fun t : ℝ => flagPs N p i hi (t • u)) 0 = 2 * tailSum p i (lowerMatrix u) := by
  simp only [flagPs_smul]
  obtain ⟨h0, h1, h2⟩ := coeff_det_one_add_X_sq_smul (kerPoly p i hi (lowerMatrix u))
  rw [deriv_deriv_log_norm_eval _ h0 h1, h2, coeff_trace_kerPoly, re_trace_sigTop_tail]

theorem contDiffAt_flagPs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → (LowerPair N → ℂ)} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0) :
    ContDiffAt ℝ 2 (fun z => flagPs N p i hi (g z)) 0 := by
  have hent : ∀ a b, ContDiff ℝ 2 fun z =>
      ((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (g z)) a b := by
    intro a b
    by_cases h : b < a
    · simp only [Matrix.add_apply, lowerMatrix, Matrix.of_apply, h, dif_pos]
      exact contDiff_const.add
        ((by fun_prop : ContDiff ℝ 2 fun f : LowerPair N → ℂ => f ⟨(a, b), h⟩).comp hg)
    · simp only [Matrix.add_apply, lowerMatrix, Matrix.of_apply, h, dif_neg, not_false_eq_true,
        add_zero]
      exact contDiff_const
  have hdet : ContDiff ℝ 2 fun z => ((((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (g z)).submatrix
      id (Fin.castLE hi)).conjTranspose * signatureForm N p *
      ((1 + lowerMatrix (g z)).submatrix id (Fin.castLE hi))).det := by
    refine contDiff_det_of_entries fun a b => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
    refine ContDiff.sum fun c _ => ContDiff.mul (ContDiff.sum fun d _ => ContDiff.mul ?_
      contDiff_const) (hent _ _)
    simpa [Function.comp_def] using Complex.conjCLE.contDiff.comp (hent d (Fin.castLE hi a))
  have h0 : ((((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (g 0)).submatrix id
      (Fin.castLE hi)).conjTranspose * signatureForm N p *
      ((1 + lowerMatrix (g 0)).submatrix id (Fin.castLE hi))).det ≠ 0 := by
    have h := det_flag_eval p i hi (0 : LowerPair N → ℂ) 0
    rw [zero_smul] at h
    rw [hg0, h, Complex.ofReal_zero, ← coeff_zero_eq_eval_zero,
      (coeff_det_one_add_X_sq_smul _).1, mul_one]
    intro h'
    have := norm_det_sigTop p i hi
    rw [h', norm_zero] at this
    exact zero_ne_one this
  unfold flagPs
  exact (ContDiffAt.norm ℝ hdet.contDiffAt h0).log (norm_ne_zero_iff.mpr h0)

end

end GroundTheory.Heights₂.Heights.FourB

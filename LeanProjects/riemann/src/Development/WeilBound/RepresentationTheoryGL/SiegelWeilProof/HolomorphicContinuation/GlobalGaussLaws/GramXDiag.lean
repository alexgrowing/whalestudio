import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfInG
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussScalar

noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS

variable {m n : ℕ}

def sigR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sigR ε a : ℝ) : ℂ) := by
  unfold sgn sigR
  by_cases h : ε a <;> simp [h]

theorem ftLoc_eq (ε : Fin m → Bool) (s : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) :
    ftLoc ε s f u = ftG (sigR ε) s f u := by
  simp only [ftLoc, ftG]
  congr 1
  funext y
  have key : ((of u)ᴴ * diagonal (sgn ε) * of y).trace.re =
      ∑ a, ∑ j, sigR ε a * ((starRingEnd ℂ) (u a j) * y a j).re := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [sgn_eq, mul_comm (star (u a j)) _, mul_assoc, Complex.re_ofReal_mul]
    rfl
  rw [key]

theorem gramX_diag (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) (j : Fin n) :
    gramX ε u j j = ∑ a, ((sigR ε a : ℝ) : ℂ) * ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, if_true,
    Bool.false_eq_true, if_false, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ε a <;> simp [h, sigR, Complex.conj_mul']

theorem chN_DG (ε : Fin m → Bool) (t : ℝ) (β : Fin n → ℝ) (K : ℂ) (γ : Fin m → Fin n → ℂ) (u : Fin m → Fin n → ℂ) :
    chN ε t (diagonal fun j => (β j : ℂ)) u * DG K γ u =
      DG K (fun a j => γ a j - I * t * (sigR ε a : ℂ) * (β j : ℂ)) u := by
  simp only [chN, DG]
  simp only [← Complex.exp_sum]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  have htr : (diagonal (fun j => (β j : ℂ)) * gramX ε u).trace = ∑ j, (β j : ℂ) * gramX ε u j j := by
    simp [Matrix.trace, Matrix.diagonal_mul]
  rw [htr]
  simp_rw [gramX_diag, Finset.mul_sum]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dg_const (K γ0 : ℂ) (v : Fin m → Fin n → ℂ) :
    DG K (fun _ _ => γ0) v = K * cexp (-γ0 * ∑ a, ∑ j, ((‖v a j‖ ^ 2 : ℝ) : ℂ)) := by
  simp only [DG]
  congr 1
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.exp_sum]

theorem vac_eq (ε : Fin m → Bool) (t c : ℝ) : vac (n := n) ε t c = DG 1 (fun _ _ => (c : ℂ)) := by
  funext y
  rw [dg_const, one_mul]
  simp only [vac, gZf]
  congr 1
  have hsum : (gramB (epsT t ε) true y).trace + (gramB (epsT t ε) false y).trace =
      ∑ a, ∑ j, ((‖y a j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, gramB, Qb, evX, map_sum, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : epsT t ε a <;> simp [h, Complex.conj_mul']
  rw [smul_mul_assoc, one_mul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    smul_mul_assoc, one_mul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_I]
  linear_combination ((c : ℂ) * ((gramB (epsT t ε) true y).trace + (gramB (epsT t ε) false y).trace)) *
    Complex.I_sq + (-(c : ℂ)) * hsum

theorem levF_diag (e : ℤ) (δ : Fin n → ℝ) (hδ : ∀ j, 0 < δ j) (K : ℂ) (γ : Fin m → Fin n → ℂ) :
    levF e (diagonal fun j => (δ j : ℂ)) (DG K γ) =
      DG (K * (∏ j, (δ j : ℂ)) ^ m) (fun a j => γ a j * ((δ j : ℂ) ^ 2)) := by
  funext u
  simp only [levF, DG, Matrix.det_diagonal]
  have hD : (∏ j, (δ j : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (hδ j).ne'
  have hs : star (∏ j, (δ j : ℂ)) = ∏ j, (δ j : ℂ) := by
    rw [← Complex.ofReal_prod]
    exact Complex.conj_ofReal _
  rw [hs, ← zpow_add₀ hD, add_sub_cancel, zpow_natCast]
  rw [← mul_assoc, mul_comm (_ ^ m) K]
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  simp only [Matrix.mul_diagonal, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.VacC

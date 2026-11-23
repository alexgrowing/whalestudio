import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LongWeylFunctional
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.GaussianMomentRealCoords

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

open Complex MvPolynomial

theorem evX_monomial (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ) (v : Fin m → Fin n → ℂ) :
    evX (monomial e c) v = c * ∏ a, ∏ j, (v a j ^ e (a, j, false) * star (v a j) ^ e (a, j, true)) := by
  simp only [evX, MvPolynomial.eval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  refine congrArg _ (Finset.prod_congr rfl fun a _ => ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Fintype.prod_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

theorem gZ_diag (sg : ℤˣ) (w : Fin n → ℂ) (v : Fin m → Fin n → ℂ) :
    gZ sg (Matrix.diagonal w) v =
      ∏ a, ∏ j, cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * w j * (normSq (v a j) : ℂ)) := by
  unfold gZ
  have h : (Matrix.diagonal w * ((Matrix.of v)ᴴ * Matrix.of v)).trace =
      ∑ a, ∑ j, w j * (normSq (v a j) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag]
    simp only [Matrix.diagonal_mul]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  rw [h, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  ring

def ker (t : ℂ) (u v : Fin m → Fin n → ℂ) : ℂ :=
  cexp (2 * Real.pi * I * ((t * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ))

theorem ker_prod (t : ℂ) (u v : Fin m → Fin n → ℂ) :
    ker t u v = ∏ a, ∏ j, cexp (2 * Real.pi * I * ((t * (star (u a j) * v a j)).re : ℂ)) := by
  unfold ker
  have h : t * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v) =
      ∑ a, ∑ j, t * (star (u a j) * v a j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h, Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Complex.re_sum, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

theorem integrand_mono (sg : ℤˣ) (t : ℂ) (z : Fin n → ℂ) (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ)
    (u v : Fin m → Fin n → ℂ) :
    ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v) =
      c * ∏ a, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (v a j) := by
  rw [ker_prod, evX_monomial, gZ_diag]
  simp only [phi1, Finset.prod_mul_distrib]
  ring

theorem intg_mono (sg : ℤˣ) (t : ℂ) (z : Fin n → ℂ) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ) (u : Fin m → Fin n → ℂ) :
    Integrable (fun v : Fin m → Fin n → ℂ => ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v)) := by
  have h : (fun v : Fin m → Fin n → ℂ => ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v)) =
      fun v => c * ∏ a, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (v a j) :=
    funext fun v => integrand_mono sg t z e c u v
  rw [h]
  refine Integrable.const_mul ?_ c
  exact Integrable.fintype_prod
    (f := fun a (w : Fin n → ℂ) => ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (w j))
    fun a => Integrable.fintype_prod
      (f := fun j w => phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) w)
      fun j => integrable_gaussian_moment sg t (z j) (u a j) (hz j) _ _

def rn (a : Fin m) (j : Fin n) (q : MvPolynomial Bool ℂ) : PX m n := rename (fun b => (a, j, b)) q

theorem four_mono (sg : ℤˣ) (t : ℂ) (z : Fin n → ℂ) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    (e : Fin m × Fin n × Bool →₀ ℕ) (c : ℂ) :
    ∃ Q : PX m n, Q.totalDegree ≤ e.sum (fun _ k => k) ∧ ∀ u, ∫ v : Fin m → Fin n → ℂ,
      ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v) =
      evX Q u * gZ sg (Matrix.diagonal fun j => -((normSq t : ℂ) / 4) * (z j)⁻¹) u := by
  choose q hqd hq using fun (a : Fin m) (j : Fin n) =>
    mom1 sg t (z j) (hz j) (e (a, j, false)) (e (a, j, true))
  refine ⟨MvPolynomial.C c * ∏ a, ∏ j, rn a j (q a j), ?_, fun u => ?_⟩
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => ?_
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Fintype.sum_bool]
    exact ((MvPolynomial.totalDegree_rename_le _ _).trans (hqd a j)).trans (le_of_eq (add_comm _ _))
  · have h : (fun v : Fin m → Fin n → ℂ => ker t u v * (evX (monomial e c) v * gZ sg (Matrix.diagonal z) v)) =
        fun v => c * ∏ a, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (v a j) :=
      funext fun v => integrand_mono sg t z e c u v
    have hin : ∀ a, ∫ w : Fin n → ℂ, ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (w j) =
        ∏ j, ((MvPolynomial.eval fun b : Bool => if b = true then star (u a j) else u a j) (q a j) *
          cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * (-((normSq t : ℂ) / 4) * (z j)⁻¹) * (normSq (u a j) : ℂ))) := by
      intro a
      rw [integral_fintype_prod_volume_eq_prod
        (fun j w => phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) w)]
      exact Finset.prod_congr rfl fun j _ => hq a j (u a j)
    rw [h, integral_const_mul, integral_fintype_prod_volume_eq_prod
      (fun a (w : Fin n → ℂ) => ∏ j, phi1 sg t (z j) (u a j) (e (a, j, false)) (e (a, j, true)) (w j))]
    simp only [hin, gZ_diag]
    simp only [evX, map_mul, map_prod, MvPolynomial.eval_C, rn, MvPolynomial.eval_rename,
      Function.comp_def, Finset.prod_mul_distrib]
    ring

end PositivityTheory.SiegelWeilFormula.KLI

end

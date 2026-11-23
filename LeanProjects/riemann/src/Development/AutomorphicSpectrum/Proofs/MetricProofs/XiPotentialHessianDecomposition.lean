import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XFibHess

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → ∃ T : Fin 3 → Matrix (Fin d) (Fin d) ℂ, ∀ a : ℂ, ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) ∧ hessC (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) = Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (-(((1 + ‖a‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => ∑ i, (((fun (a : ℂ) (i : Fin 3) => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)) a i : ℝ) : ℂ) * T i p' q') q) p := by
  intro d G y _ hC h1 h0
  let A : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ := fun p q => fderiv ℝ (fderiv ℝ fun y' => (G y' p q).re) y
  let B : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ := fun p q => fderiv ℝ (fderiv ℝ fun y' => (G y' p q).im) y
  refine ⟨![PositivityTheory.Xgp.fib_hess.hm ((-(1/2:ℝ)) • (A 0 1 + A 1 0)), PositivityTheory.Xgp.fib_hess.hm ((-(1/2:ℝ)) • (B 1 0 - B 0 1)), PositivityTheory.Xgp.fib_hess.hm ((1/2:ℝ) • (A 1 1 - A 0 0))], fun a => ?_⟩
  obtain ⟨hc, hH⟩ := PositivityTheory.Xgp.fib_hess.jet d G y hC h1 h0 a A B (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨hc, ?_⟩
  ext p q
  refine Fin.cases ?_ (fun p' => ?_) p <;> refine Fin.cases ?_ (fun q' => ?_) q
  all_goals simp only [hessC, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, hH, PositivityTheory.Xgp.fib_hess.tl_zero, PositivityTheory.Xgp.fib_hess.tl_zero', PositivityTheory.Xgp.fib_hess.tl_succ, PositivityTheory.Xgp.fib_hess.tl_succ', map_zero, ContinuousLinearMap.zero_apply]
  all_goals simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, ne_eq, Fin.succ_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, mul_one, Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  all_goals clear hH hc h0 h1 hC
  all_goals have hr : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  all_goals have hpos : (0:ℝ) < 1 + (a.re ^ 2 + a.im ^ 2) := by positivity
  all_goals have hne : (1 + ((a.re:ℂ) ^ 2 + (a.im:ℂ) ^ 2)) ≠ 0 := by exact_mod_cast hpos.ne'
  case refine_1.refine_1 =>
    rw [hr]
    push_cast
    field_simp
    ring
  all_goals have hz : ∀ j : Fin d, (Pi.single j.succ (1:ℂ) : Fin (d+1) → ℂ) 0 = 0 := fun j => by simp [Pi.single_apply, (Fin.succ_ne_zero j).symm]
  all_goals simp only [hz, mul_zero, Complex.zero_re, Complex.zero_im, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PositivityTheory.Xgp.fib_hess.hm, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.neg_apply]
  all_goals try rw [hr]
  case refine_2.refine_2 =>
    apply Complex.ext
    · simp only [Complex.add_re, Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.div_im, Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.normSq_ofNat]
      field_simp
      ring
    · simp only [Complex.add_re, Complex.div_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.div_im, Complex.mul_im, Complex.sub_im, Complex.neg_im, Complex.normSq_ofNat]
      field_simp
      ring
  all_goals push_cast
  all_goals field_simp
  all_goals ring

import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GramXApply

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem norm_scal_sq (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) (s : ℝ) (a : Fin m) (j : Fin n) :
    ‖scal (aH X s) y a j‖ ^ 2 = Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2 := by
  simp only [scal, aH, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]

theorem hasDerivAt_gs (c : ℝ) (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) (h : ℝ) :
    HasDerivAt (fun s => gs c (scal (aH X s) y))
      (gs c (scal (aH X h) y) * (-(((c * ∑ a, ∑ j, 2 * X j * ‖scal (aH X h) y a j‖ ^ 2) : ℝ) : ℂ))) h := by
  have key : ∀ s : ℝ, gs c (scal (aH X s) y) =
      Complex.exp (-(((c * ∑ a, ∑ j, Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2 : ℝ)) : ℂ)) := by
    intro s
    simp only [gs, norm_scal_sq]
  have hF : HasDerivAt (fun s : ℝ => c * ∑ a, ∑ j, Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2)
      (c * ∑ a, ∑ j, 2 * X j * (Real.exp (h * X j) ^ 2 * ‖y a j‖ ^ 2)) h := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro a _
    apply HasDerivAt.fun_sum
    intro j _
    have e : HasDerivAt (fun s : ℝ => Real.exp (s * X j)) (Real.exp (h * X j) * X j) h := by
      simpa using ((hasDerivAt_id h).mul_const (X j)).exp
    exact ((e.pow 2).mul_const (‖y a j‖ ^ 2)).congr_deriv (by
      rw [show (2 : ℕ) - 1 = 1 from rfl]
      push_cast
      ring)
  have hc := (hF.ofReal_comp.neg).cexp
  rw [show (fun s : ℝ => gs c (scal (aH X s) y)) = fun s : ℝ =>
      Complex.exp (-(((c * ∑ a, ∑ j, Real.exp (s * X j) ^ 2 * ‖y a j‖ ^ 2 : ℝ)) : ℂ)) from funext key]
  refine hc.congr_deriv ?_
  rw [key h]
  simp only [norm_scal_sq, Pi.neg_apply]

theorem hasDerivAt_phi (c : ℝ) (X : Fin n → ℝ) (Q : PX m n) (y : Fin m → Fin n → ℂ) (h : ℝ) :
    HasDerivAt (fun s => evX Q (scal (aH X s) y) * gs c (scal (aH X s) y))
      ((evX (dil c X Q) (scal (aH X h) y) - ((m : ℂ) * ∑ j, (X j : ℂ)) * evX Q (scal (aH X h) y)) *
        gs c (scal (aH X h) y)) h := by
  have h1 : HasDerivAt (fun s : ℝ => evX Q (scal (aH X s) y))
      (∑ k, eval (ept (scal (aH X h) y)) (pderiv k Q) * ((X k.2.1 : ℂ) * ept (scal (aH X h) y) k)) h := by
    simp only [evX_eq]
    exact hasDerivAt_eval_curve Q (fun s => ept (scal (aH X s) y)) _ h
      (fun k => hasDerivAt_scal_coord X y h k)
  exact (h1.mul (hasDerivAt_gs c X y h)).congr_deriv (by
    rw [evX_dil]
    push_cast
    ring)

private theorem dom_bound_lemma (X : Fin n → ℝ) (h : ℝ) (hh : |h| < 1) (j : Fin n) :
    Real.exp (-(∑ i, |X i|)) ≤ Real.exp (h * X j) ∧ Real.exp (h * X j) ≤ Real.exp (∑ i, |X i|) := by
  have hj : |X j| ≤ ∑ i, |X i| :=
    Finset.single_le_sum (f := fun i => |X i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hx : |h * X j| ≤ ∑ i, |X i| := by
    rw [abs_mul]
    calc |h| * |X j| ≤ 1 * |X j| := mul_le_mul_of_nonneg_right hh.le (abs_nonneg _)
      _ ≤ ∑ i, |X i| := by simpa using hj
  constructor
  · exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (h * X j)])
  · exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hx)

private theorem dom_bound_lemma_2 (X : Fin n → ℝ) (h : ℝ) (hh : |h| < 1) (y : Fin m → Fin n → ℂ) :
    ‖scal (aH X h) y‖ ≤ Real.exp (∑ i, |X i|) * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  have e := (dom_bound_lemma X h hh j).2
  have hy : ‖y a j‖ ≤ ‖y‖ := (norm_le_pi_norm (y a) j).trans (norm_le_pi_norm y a)
  have hn : ‖scal (aH X h) y a j‖ = Real.exp (h * X j) * ‖y a j‖ := by
    simp only [scal, aH, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hn]
  exact mul_le_mul e hy (norm_nonneg _) (Real.exp_pos _).le

private theorem dom_bound_lemma_3 (X : Fin n → ℝ) (h : ℝ) (hh : |h| < 1) (y : Fin m → Fin n → ℂ) :
    Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2 ≤ ∑ a, ∑ j, ‖scal (aH X h) y a j‖ ^ 2 := by
  calc Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2
        ≤ Real.exp (-(∑ i, |X i|)) ^ 2 * ∑ a, ∑ j, ‖y a j‖ ^ 2 := by
          gcongr
          exact sq_norm_le_sum y
    _ = ∑ a, ∑ j, Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y a j‖ ^ 2 := by
          simp only [Finset.mul_sum]
    _ ≤ ∑ a, ∑ j, ‖scal (aH X h) y a j‖ ^ 2 := by
          gcongr with a _ j _
          rw [norm_scal_sq]
          gcongr
          exact Real.exp_le_exp.mp (dom_bound_lemma X h hh j).1

theorem dom_bound (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (P : PX m n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, |h| < 1 → ∀ y : Fin m → Fin n → ℂ,
      ‖evX P (scal (aH X h) y) * gs c (scal (aH X h) y)‖ ≤
        K * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by
  obtain ⟨C, k, hC, hP⟩ := poly_bound P
  have hM0 : 0 ≤ ∑ i, |X i| := Finset.sum_nonneg fun i _ => abs_nonneg (X i)
  have hκ : 0 < c * Real.exp (-(∑ i, |X i|)) ^ 2 := by positivity
  obtain ⟨D, hD, hdec⟩ := decay k _ hκ ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)
  refine ⟨C * Real.exp (∑ i, |X i|) ^ k * D, by positivity, fun h hh y => ?_⟩
  have hv := dom_bound_lemma_2 X h hh y
  have hs := dom_bound_lemma_3 X h hh y
  have hg : ‖gs c (scal (aH X h) y)‖ ≤
      Real.exp (-(c * Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2)) := by
    rw [gs, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hs hc.le]
  have hp : ‖evX P (scal (aH X h) y)‖ ≤ C * Real.exp (∑ i, |X i|) ^ k * (1 + ‖y‖) ^ k := by
    calc ‖evX P (scal (aH X h) y)‖ ≤ C * (1 + ‖scal (aH X h) y‖) ^ k := hP _
      _ ≤ C * (Real.exp (∑ i, |X i|) * (1 + ‖y‖)) ^ k := by
          gcongr
          have : 1 ≤ Real.exp (∑ i, |X i|) := Real.one_le_exp hM0
          nlinarith [norm_nonneg y]
      _ = C * Real.exp (∑ i, |X i|) ^ k * (1 + ‖y‖) ^ k := by
          rw [mul_pow, mul_assoc]
  calc ‖evX P (scal (aH X h) y) * gs c (scal (aH X h) y)‖
        = ‖evX P (scal (aH X h) y)‖ * ‖gs c (scal (aH X h) y)‖ := norm_mul _ _
    _ ≤ (C * Real.exp (∑ i, |X i|) ^ k * (1 + ‖y‖) ^ k) *
          Real.exp (-(c * Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2)) := by
          gcongr
    _ = C * Real.exp (∑ i, |X i|) ^ k *
          ((1 + ‖y‖) ^ k * Real.exp (-(c * Real.exp (-(∑ i, |X i|)) ^ 2 * ‖y‖ ^ 2))) := by ring
    _ ≤ C * Real.exp (∑ i, |X i|) ^ k *
          (D * (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (hdec _ (norm_nonneg y)) (by positivity)
    _ = C * Real.exp (∑ i, |X i|) ^ k * D *
          (1 + ‖y‖) ^ (-((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1)) := by ring

end PositivityTheory.Rg.Sw.AbsSt.DF

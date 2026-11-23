import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureA
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.MaDiag

theorem matrix_eq_of_form {e : ℕ} (A B : Matrix (Fin e) (Fin e) ℂ)
    (h : ∀ w : Fin e → ℂ, w ⬝ᵥ (A *ᵥ star w) = w ⬝ᵥ (B *ᵥ star w)) : A = B := by
  set C := A - B with hC
  have hΦ : ∀ w : Fin e → ℂ, w ⬝ᵥ (C *ᵥ star w) = 0 := by
    intro w
    rw [hC, Matrix.sub_mulVec, dotProduct_sub, h w, sub_self]
  have expand : ∀ (u w : Fin e → ℂ) (c : ℂ), (u + c • w) ⬝ᵥ (C *ᵥ star (u + c • w)) =
      u ⬝ᵥ (C *ᵥ star u) + star c * (u ⬝ᵥ (C *ᵥ star w)) + c * (w ⬝ᵥ (C *ᵥ star u)) +
        c * star c * (w ⬝ᵥ (C *ᵥ star w)) := by
    intro u w c
    simp only [star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hsI : (star Complex.I : ℂ) = -Complex.I := Complex.conj_I
  have hpair : ∀ u w : Fin e → ℂ, u ⬝ᵥ (C *ᵥ star w) = 0 := by
    intro u w
    have h1 := expand u w 1
    have h2 := expand u w Complex.I
    rw [hΦ (u + (1 : ℂ) • w), hΦ u, hΦ w, star_one] at h1
    rw [hΦ (u + Complex.I • w), hΦ u, hΦ w, hsI] at h2
    linear_combination (-1 / 2 : ℂ) * h1 + (-Complex.I / 2) * h2 +
      ((u ⬝ᵥ (C *ᵥ star w) - w ⬝ᵥ (C *ᵥ star u)) / 2) * Complex.I_sq
  ext i j
  have hs : star (Pi.single j (1 : ℂ) : Fin e → ℂ) = Pi.single j 1 := by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have := hpair (Pi.single i 1) (Pi.single j 1)
  rw [hs] at this
  simpa [C, sub_eq_zero] using this

private theorem pair_inv_mul_eq_of_mul_self_eq_one (c d : ℂ) (a b p q : ℝ) :
    c * ((((a + q : ℝ) : ℂ) + Complex.I * ((b - p : ℝ) : ℂ)) / 4 * star d) =
      ((((c.re * d.re * a + c.re * d.im * b + c.im * d.re * p + c.im * d.im * q) +
        ((Complex.I * c).re * (Complex.I * d).re * a + (Complex.I * c).re * (Complex.I * d).im * b +
          (Complex.I * c).im * (Complex.I * d).re * p +
            (Complex.I * c).im * (Complex.I * d).im * q)) / 4 : ℝ) : ℂ) +
      Complex.I * ((((c.re * (Complex.I * d).re * a + c.re * (Complex.I * d).im * b +
          c.im * (Complex.I * d).re * p + c.im * (Complex.I * d).im * q) -
        ((Complex.I * c).re * d.re * a + (Complex.I * c).re * d.im * b +
          (Complex.I * c).im * d.re * p + (Complex.I * c).im * d.im * q)) / 4 : ℝ) : ℂ) := by
  have h4 : ∀ X : ℂ, X / 4 = ((1 / 4 : ℝ) : ℂ) * X := fun X => by push_cast; ring
  rw [h4]
  apply Complex.ext <;> simp <;> ring

theorem dot_hessC_star {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (w : Fin e → ℂ) :
    w ⬝ᵥ (hessC f z *ᵥ star w) = (levi f z w : ℂ) := by
  set H := fderiv ℝ (fderiv ℝ f) z with hH
  have hsymm : ∀ x y, H x y = H y x := fun x y =>
    hf.isSymmSndFDerivAt minSmoothness_of_isRCLikeNormedField.le x y
  have hsmul : ∀ (c : ℂ) (u : Fin e → ℂ), c • u = c.re • u + c.im • (Complex.I • u) := by
    intro c u
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hHs : ∀ (c d : ℂ) (u v : Fin e → ℂ), H (c • u) (d • v) =
      c.re * d.re * H u v + c.re * d.im * H u (Complex.I • v) +
        c.im * d.re * H (Complex.I • u) v + c.im * d.im * H (Complex.I • u) (Complex.I • v) := by
    intro c d u v
    rw [hsmul c u, hsmul d v]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul]
    ring
  set E := fun i : Fin e => (Pi.single i (1 : ℂ) : Fin e → ℂ) with hE
  have hw : ∀ x : Fin e → ℂ, x = ∑ i, x i • E i := by
    intro x
    ext k
    simp [hE, Finset.sum_apply, Pi.single_apply]
  have hHsum : ∀ x y : Fin e → ℂ, H x y = ∑ i, ∑ j, H (x i • E i) (y j • E j) := by
    intro x y
    conv_lhs => rw [hw x, hw y]
    simp only [map_sum, ContinuousLinearMap.sum_apply]
    exact Finset.sum_comm
  have hpair : ∀ i j, w i * (hessC f z i j * star (w j)) =
      (((H (w i • E i) (w j • E j) + H ((Complex.I * w i) • E i) ((Complex.I * w j) • E j)) / 4 : ℝ) : ℂ) +
        Complex.I * (((H (w i • E i) ((Complex.I * w j) • E j) -
          H ((Complex.I * w i) • E i) (w j • E j)) / 4 : ℝ) : ℂ) := by
    intro i j
    have hx : hessC f z i j = (((H (E i) (E j) + H (Complex.I • E i) (Complex.I • E j) : ℝ) : ℂ) +
        Complex.I * ((H (E i) (Complex.I • E j) - H (Complex.I • E i) (E j) : ℝ) : ℂ)) / 4 := rfl
    rw [hx, hHs (w i) (w j), hHs (Complex.I * w i) (Complex.I * w j), hHs (w i) (Complex.I * w j),
      hHs (Complex.I * w i) (w j)]
    exact pair_inv_mul_eq_of_mul_self_eq_one (w i) (w j) _ _ _ _
  have hanti : ∀ F : Fin e → Fin e → ℝ, (∀ i j, F i j = -F j i) → ∑ i, ∑ j, F i j = 0 := by
    intro F hF
    have h1 : ∑ i, ∑ j, F i j = ∑ j, ∑ i, F i j := Finset.sum_comm
    have h2 : ∑ j, ∑ i, F i j = -∑ j, ∑ i, F j i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => hF i j)
    linarith
  have hQ0 : ∑ i, ∑ j, ((H (w i • E i) ((Complex.I * w j) • E j) -
      H ((Complex.I * w i) • E i) (w j • E j)) / 4 : ℝ) = 0 := by
    apply hanti
    intro i j
    rw [hsymm (w i • E i), hsymm ((Complex.I * w i) • E i)]
    ring
  have hLHS : w ⬝ᵥ (hessC f z *ᵥ star w) = ∑ i, ∑ j, w i * (hessC f z i j * star (w j)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  have hlevi : levi f z w = (H w w + H (Complex.I • w) (Complex.I • w)) / 4 := rfl
  rw [hLHS]
  simp_rw [hpair]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [hQ0, Complex.ofReal_zero, mul_zero, add_zero, hlevi, hHsum w w,
    hHsum (Complex.I • w) (Complex.I • w)]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]

theorem dot_congr_diag {e : ℕ} (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ) (w : Fin e → ℂ) :
    w ⬝ᵥ ((Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ)) *ᵥ star w) =
      ((∑ q, dd q * ‖(M *ᵥ w) q‖ ^ 2 : ℝ) : ℂ) := by
  have hs : M.map (starRingEnd ℂ) *ᵥ star w = star (M *ᵥ w) := by
    ext q
    simp [Matrix.mulVec, dotProduct, star_sum]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro q _
  rw [← Complex.mul_conj']
  simp only [Complex.star_def]
  ring

theorem det_congr_diag {e : ℕ} (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ) :
    (Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ)).det =
      (((∏ q, dd q) * ‖M.det‖ ^ 2 : ℝ) : ℂ) := by
  have hc : (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hc]
  push_cast
  rw [← Complex.mul_conj']
  ring

theorem maDens_diag_levi (e : ℕ) (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (dd : Fin e → ℝ)
    (M : Matrix (Fin e) (Fin e) ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hl : ∀ v, levi φ z v = ∑ q, dd q * ‖(M *ᵥ v) q‖ ^ 2) :
    maDens (fun _ => φ) z =
      (e.factorial : ℝ) * (2 / Real.pi) ^ e * (∏ q, dd q) * ‖M.det‖ ^ 2 := by
  have hH : hessC φ z = Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ) := by
    apply matrix_eq_of_form
    intro w
    rw [dot_hessC_star φ z hφ w, dot_congr_diag, hl w]
  simp only [maDens]
  rw [hH, ReciprocityTheory.AnForm.A.mdisc_const, det_congr_diag, Complex.ofReal_re]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.MaDiag

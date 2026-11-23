import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartDensityIntegrable
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartMassAffine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartDensityIntegrableAlt

theorem exists_conjTranspose_mul_self {e : ℕ} {N : Matrix (Fin e) (Fin e) ℂ} (hN : N.PosDef) :
    ∃ C : Matrix (Fin e) (Fin e) ℂ, N = Cᴴ * C ∧ C.det ≠ 0 := by
  obtain ⟨U, l, hl, hspec⟩ : ∃ (U : Matrix (Fin e) (Fin e) ℂ) (l : Fin e → ℝ), (∀ k, 0 ≤ l k) ∧
      N = U * diagonal (fun k => (l k : ℂ)) * star U := by
    refine ⟨(hN.1.eigenvectorUnitary : Matrix (Fin e) (Fin e) ℂ), hN.1.eigenvalues,
      fun k => (hN.eigenvalues_pos k).le, ?_⟩
    have h := hN.1.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h
    exact h
  set s : Fin e → ℂ := fun k => ((Real.sqrt (l k) : ℝ) : ℂ) with hs
  have hss : (fun i => star s i * s i) = fun k => (l k : ℂ) := by
    funext k
    simp only [hs, Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hl k)]
  have hNC : N = (diagonal s * star U)ᴴ * (diagonal s * star U) := by
    rw [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose, diagonal_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal (star s)), diagonal_mul_diagonal, hss, hspec,
      star_eq_conjTranspose, Matrix.mul_assoc]
  refine ⟨diagonal s * star U, hNC, fun h => ?_⟩
  have hdet := (hN.det_pos).ne'
  rw [hNC, det_mul, h, mul_zero] at hdet
  exact hdet rfl

theorem chart_quad_eq {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hH : M.IsHermitian)
    {C : Matrix (Fin e) (Fin e) ℂ} (hNC : M.submatrix Fin.succ Fin.succ = Cᴴ * C) {d : Fin e → ℂ}
    (hd : Cᴴ *ᵥ d = fun i => M i.succ 0) (y : Fin e → ℂ) :
    star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) =
      (M 0 0 - star d ⬝ᵥ d) + star (C *ᵥ y + d) ⬝ᵥ (C *ᵥ y + d) := by
  have h1 : star (C *ᵥ y + d) ⬝ᵥ (C *ᵥ y + d) =
      star y ⬝ᵥ ((Cᴴ * C) *ᵥ y) + star y ⬝ᵥ (Cᴴ *ᵥ d) + star (Cᴴ *ᵥ d) ⬝ᵥ y + star d ⬝ᵥ d := by
    rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, star_mulVec, ← dotProduct_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec, dotProduct_mulVec (star d) C y]
    ring
  rw [h1, ← hNC, hd]
  have hw : ∀ j : Fin e, M 0 j.succ = star (M j.succ 0) := fun j => (hH.apply 0 j.succ).symm
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.star_apply, star_one,
    one_mul, mul_one, submatrix_apply, hw, mul_add, Finset.sum_add_distrib]
  ring

theorem re_star_dotProduct_self {e : ℕ} (z : Fin e → ℂ) : (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem hermChartPot_eq_gbPot_affine {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ∃ (c : Fin e → ℂ) (P : Matrix (Fin e) (Fin e) ℂ) (κ : ℝ), P.det ≠ 0 ∧
      hermChartPot M = fun y => gbPot (c + P *ᵥ y) + κ := by
  obtain ⟨C, hNC, hC⟩ := exists_conjTranspose_mul_self (hM.submatrix (Fin.succ_injective e))
  have hCH : Cᴴ.det ≠ 0 := by rw [det_conjTranspose]; exact star_ne_zero.mpr hC
  set w : Fin e → ℂ := fun i => M i.succ 0 with hw
  set d : Fin e → ℂ := (Cᴴ)⁻¹ *ᵥ w with hd'
  have hd : Cᴴ *ᵥ d = w := by
    rw [hd', mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hCH), one_mulVec]
  have hq := fun y => chart_quad_eq hM.1 hNC hd y
  set s : ℝ := (M 0 0 - star d ⬝ᵥ d).re with hs
  have hspos : 0 < s := by
    have hy0 : C *ᵥ (-(C⁻¹ *ᵥ d)) + d = 0 := by
      rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC), one_mulVec, neg_add_cancel]
    have hx : (Fin.cons 1 (-(C⁻¹ *ᵥ d)) : Fin (e + 1) → ℂ) ≠ 0 := fun h => by
      have := congr_fun h 0
      simp at this
    have hpos := hM.re_dotProduct_pos hx
    rw [hq, hy0] at hpos
    simpa [hs] using hpos
  set r : ℝ := Real.sqrt s with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hspos
  refine ⟨((r⁻¹ : ℝ) : ℂ) • d, ((r⁻¹ : ℝ) : ℂ) • C, Real.log r, ?_, ?_⟩
  · rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (inv_pos.mpr hrpos).ne')) hC
  · funext y
    have hX : 0 ≤ ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by positivity
    have hcy : ((r⁻¹ : ℝ) : ℂ) • d + (((r⁻¹ : ℝ) : ℂ) • C) *ᵥ y = ((r⁻¹ : ℝ) : ℂ) • (C *ᵥ y + d) := by
      rw [smul_mulVec, smul_add, add_comm]
    have hnorm : ∑ i, ‖(((r⁻¹ : ℝ) : ℂ) • (C *ᵥ y + d)) i‖ ^ 2 = (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hrpos), mul_pow]
    have hsq : s = r ^ 2 := (Real.sq_sqrt hspos.le).symm
    have h1pos : 0 < 1 + (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by positivity
    have hsplit : s + ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 = r ^ 2 * (1 + (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2) := by
      rw [hsq]; field_simp
    simp only [hermChartPot, gbPot]
    rw [hq, Complex.add_re, ← hs, re_star_dotProduct_self, hcy, hnorm, hsplit,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hrpos.le,
      Real.log_mul hrpos.ne' (Real.sqrt_pos.mpr h1pos).ne']
    ring

theorem integrable_fsDens (D : ℕ) :
    Integrable (fun y : Fin D → ℂ => ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹) := by
  have hcont : Continuous (fun y : Fin D → ℂ => ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun y => ?_
    have : 0 < 1 + ∑ i, ‖y i‖ ^ 2 := by positivity
    positivity
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by
    simp only [Pi.zero_apply]; positivity)]
  have h := gaM_lintegral_pi D 1 one_pos 0
  simp only [add_zero] at h
  rw [h]
  exact ENNReal.ofReal_lt_top

theorem integrable_comp_affine {D : ℕ} {f : (Fin D → ℂ) → ℝ} (hf : Integrable f) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) : Integrable (fun y => f (c + P *ᵥ y)) := by
  set L := ChartMongeAmpereAffineInvariance.realCLE P hP
  have hpos : 0 < Complex.normSq P.det := Complex.normSq_pos.mpr hP
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin D → ℂ))
    (f := ((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)))
    (by rw [ChartMongeAmpereAffineInvariance.det_realCLE]; exact hpos.ne')
  have hcoe : ⇑((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) = ⇑L := rfl
  rw [hcoe] at hmap
  have hg : Integrable (fun w => f (c + w)) (Measure.map L volume) := by
    rw [hmap]
    exact (hf.comp_add_left c).smul_measure ENNReal.ofReal_ne_top
  exact L.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hg

end ChartDensityIntegrableAlt

open ChartDensityIntegrableAlt in

theorem ChartDensityIntegrable.proof : ChartDensityIntegrable.Statement := by
  intro e M hM
  obtain ⟨c, P, κ, hP, hpot⟩ := hermChartPot_eq_gbPot_affine M hM
  have h : (fun y : Fin e → ℂ => maDensity (fun _ : Fin e => hermChartPot M) y) = fun y =>
      (Complex.normSq P.det * ((e.factorial : ℝ) / Real.pi ^ e)) *
        ((1 + ∑ i, ‖(c + P *ᵥ y) i‖ ^ 2) ^ (e + 1))⁻¹ := by
    funext y
    rw [hpot, ChartMongeAmpereAffineInvariance.maDensity_comp_affine gbPot c P hP κ y, maDensity_gbPot]
    ring
  rw [h]
  exact (integrable_comp_affine (integrable_fsDens e) c P hP).const_mul _

end

end GroundTheory.Heights₂.Heights

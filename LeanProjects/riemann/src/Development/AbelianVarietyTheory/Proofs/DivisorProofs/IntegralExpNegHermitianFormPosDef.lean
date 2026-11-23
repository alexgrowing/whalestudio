import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory.GaussHerm

lemma finrank_V (n : ℕ) : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

lemma det_toEuclideanLin {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (Matrix.toEuclideanLin C) = C.det := by
  have : Matrix.toEuclideanLin C = Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis C := by
    ext v i : 2
    simp [Matrix.toLin_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
      EuclideanSpace.single_apply, Pi.single_apply]
  rw [this, LinearMap.det_toLin]

lemma quad_eq {n : ℕ} (H C : Matrix (Fin n) (Fin n) ℂ) (hC : H.transpose = C.conjTranspose * C)
    (w : V n) :
    (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re = ‖Matrix.toEuclideanLin C w‖ ^ 2 := by
  have hH : ∀ j l, H j l = ∑ k, (starRingEnd ℂ) (C k l) * C k j := by
    intro j l
    have := congrFun (congrFun hC l) j
    simpa [Matrix.mul_apply] using this
  have hc : (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)) =
      ∑ k, (∑ j, C k j * w j) * (starRingEnd ℂ) (∑ l, C k l * w l) := by
    simp only [hH, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans (Finset.sum_comm.trans
      (Finset.sum_congr rfl fun k _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun j _ => by ring)))
  rw [hc, EuclideanSpace.norm_sq_eq, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]

theorem exists_eq_conjTranspose_mul_self {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.PosSemidef) : ∃ B : Matrix (Fin n) (Fin n) ℂ, T = B.conjTranspose * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩

theorem integral_exp_neg_herm : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.PosDef →
    Integrable (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) ∧
    ∫ w : V n, Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re) =
      Real.pi ^ n / H.det.re := by
  intro n H hH
  have hT : H.transpose.PosDef := Matrix.PosDef.transpose_iff.mpr hH
  obtain ⟨C, hC⟩ := exists_eq_conjTranspose_mul_self hT.posSemidef
  set L : V n →ₗ[ℝ] V n := (Matrix.toEuclideanLin C).restrictScalars ℝ with hL
  have hdetL : LinearMap.det L = Complex.normSq C.det := by
    rw [hL, LinearMap.det_restrictScalars, det_toEuclideanLin, Algebra.norm_complex_apply]
  have hdetC : H.det = (Complex.normSq C.det : ℂ) := by
    rw [← Matrix.det_transpose H, hC, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      mul_comm, Complex.mul_conj]
  have hdetH : H.det.re = Complex.normSq C.det := by rw [hdetC, Complex.ofReal_re]
  have hpos : 0 < Complex.normSq C.det := by
    have := hH.det_pos
    rwa [hdetC, Complex.zero_lt_real] at this
  set g : V n → ℝ := fun v => Real.exp (-1 * ‖v‖ ^ 2) with hg
  have hf : (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) =
      fun w => g (L w) := by
    funext w
    rw [quad_eq H C hC w, hg]
    simp [hL]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (V n)) (f := L)
    (by rw [hdetL]; exact hpos.ne')
  have hG : ∫ v : V n, g v = Real.pi ^ n := by
    rw [hg, GaussianFourier.integral_rexp_neg_mul_sq_norm one_pos, finrank_V, div_one]
    rw [show ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hI : ∫ w : V n, g (L w) = Real.pi ^ n / H.det.re := by
    rw [← integral_map (L.continuous_of_finiteDimensional.aemeasurable)
      hgc.aestronglyMeasurable, hmap, integral_smul_measure, hG, hdetL, hdetH,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr hpos), smul_eq_mul,
      div_eq_inv_mul]
  rw [hf]
  refine ⟨Integrable.of_integral_ne_zero ?_, hI⟩
  rw [hI, hdetH]
  exact (div_pos (pow_pos Real.pi_pos n) hpos).ne'

end GlobalTheory.GaussHerm

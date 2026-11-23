import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex
open scoped Matrix

noncomputable section

variable {ι : Type} [Fintype ι]

lemma lemS_Hf_im (x y : EuclideanSpace ℂ ι) :
    (Hf x y).im = inner ℝ y ((-I : ℂ) • x) := by
  simp only [Hf, PiLp.inner_apply, PiLp.smul_apply, smul_eq_mul, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
    | rw [Complex.inner]
    | rw [real_inner_eq_re_inner ℂ]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, RCLike.re_to_complex,
    RCLike.inner_apply]
  ring

def lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι :=
  ((-I : ℂ) • (LinearMap.id : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)).restrictScalars ℝ

lemma lemSJ_apply (x : EuclideanSpace ℂ ι) : (lemSJ : _ →ₗ[ℝ] _) x = (-I : ℂ) • x := rfl

lemma lemSJ_det : |LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _)| = 1 := by
  have h2 : ∀ x : EuclideanSpace ℂ ι, (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (lemSJ x) = -x := by
    intro x
    rw [lemSJ_apply, lemSJ_apply, smul_smul, neg_mul_neg, Complex.I_mul_I, neg_one_smul]
  have hJJ : (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) * lemSJ = -1 :=
    LinearMap.ext fun x => h2 x
  have h4 : (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) ^ 4 = 1 := by
    have e : (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) ^ 4 = (lemSJ * lemSJ) * (lemSJ * lemSJ) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e, hJJ, neg_one_mul, neg_neg]
  have hd : LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) ^ 4 = 1 := by
    rw [← map_pow, h4, map_one]
  have ha : |LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _)| ^ 4 = 1 := by
    rw [← abs_pow, hd, abs_one]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by norm_num)).1 ha

lemma lemS_Hf_sum {n : ℕ} (c : Fin n → ℤ) (v : Fin n → EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ ι) :
    (Hf (∑ i, c i • v i) y).im = ∑ i, (c i : ℝ) * (Hf (v i) y).im := by
  rw [lemS_Hf_im]
  simp only [lemS_Hf_im, Finset.smul_sum, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]

def lemSG {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => (Hf (b i) (b k)).im

lemma lemSG_det {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι))
    (b₀ : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℂ ι)) :
    (lemSG b).det = LinearMap.det (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) *
      b₀.toBasis.det b * b₀.toBasis.det b := by
  have hG : lemSG b = (b₀.toBasis.toMatrix b)ᵀ *
      (LinearMap.toMatrix b₀.toBasis b₀.toBasis (lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _))ᵀ *
      b₀.toBasis.toMatrix b := by
    ext i k
    have e1 : lemSG b i k = inner ℝ (b k) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b i)) := by
      simp only [lemSG, Matrix.of_apply, lemS_Hf_im, lemSJ_apply]
    have e2 : ∀ j, inner ℝ (b₀ j) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b i)) =
        ∑ l, inner ℝ (b₀ j) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b₀ l)) * inner ℝ (b₀ l) (b i) := by
      intro j
      conv_lhs => rw [← b₀.sum_repr' (b i)]
      rw [map_sum, inner_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, real_inner_smul_right, mul_comm]
    rw [e1, ← b₀.sum_inner_mul_inner (b k) ((lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] _) (b i))]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.coe_toBasis, e2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum, real_inner_comm (b₀ j) (b k)]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
    LinearMap.det_toMatrix, Module.Basis.det_apply]
  ring

set_option maxHeartbeats 800000 in

lemma lemSG_inv (Y : GT ι) :
    ∃ C : Matrix (Fin (2 * Fintype.card ι)) (Fin (2 * Fintype.card ι)) ℤ,
      (C.map (Int.cast : ℤ → ℝ)) * lemSG Y.b = 1 := by
  classical
  have hx : ∀ k, ∃ x ∈ lat Y.b, ∀ y : lat Y.b,
      ((((Y.b.restrictScalars ℤ).coord k).toAddMonoidHom y : ℤ) : ℝ) =
        (Hf x (y : EuclideanSpace ℂ ι)).im :=
    fun k => Y.perfect _
  choose x hxl hxφ using hx
  refine ⟨Matrix.of fun k i => (Y.b.restrictScalars ℤ).repr ⟨x k, hxl k⟩ i, ?_⟩
  ext k m
  have hsum : x k = ∑ i, ((Y.b.restrictScalars ℤ).repr ⟨x k, hxl k⟩ i) • Y.b i := by
    have h := congrArg (fun v : lat Y.b => (v : EuclideanSpace ℂ ι))
      ((Y.b.restrictScalars ℤ).sum_repr ⟨x k, hxl k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Module.Basis.restrictScalars_apply] at h
    exact h.symm
  have h2 : (Hf (x k) (Y.b m)).im =
      ∑ i, (((Y.b.restrictScalars ℤ).repr ⟨x k, hxl k⟩ i : ℤ) : ℝ) * (Hf (Y.b i) (Y.b m)).im := by
    conv_lhs => rw [hsum]
    exact lemS_Hf_sum _ _ _
  have h3 : (Hf (x k) (Y.b m)).im =
      ((((Y.b.restrictScalars ℤ).coord k) ((Y.b.restrictScalars ℤ) m) : ℤ) : ℝ) := by
    have h := hxφ k ((Y.b.restrictScalars ℤ) m)
    rw [LinearMap.toAddMonoidHom_coe, Module.Basis.restrictScalars_apply] at h
    exact h.symm
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, lemSG, Matrix.one_apply]
  rw [← h2, h3, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rcases eq_or_ne k m with rfl | hkm
  · simp
  · simp [hkm, Ne.symm hkm]

lemma lemS_detM_le (Y : GT ι) (b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι)) :
    |b₀.toBasis.det Y.b| ≤ 1 := by
  obtain ⟨C, hC⟩ := lemSG_inv Y
  have hdet := congrArg Matrix.det hC
  rw [Matrix.det_mul, Matrix.det_one, lemSG_det Y.b b₀, ← Int.cast_det] at hdet
  have hJ := lemSJ_det (ι := ι)
  have hC0 : C.det ≠ 0 := by
    rintro h
    rw [h] at hdet
    simp at hdet
  have h1 : (1 : ℝ) ≤ |(C.det : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hC0
  have habs := congrArg abs hdet
  simp only [abs_mul, abs_one, hJ, one_mul] at habs
  nlinarith [abs_nonneg (b₀.toBasis.det Y.b), mul_nonneg (sub_nonneg.2 h1)
    (mul_self_nonneg |b₀.toBasis.det Y.b|)]

lemma lemS_vol_le (Y : GT ι) : volume (ZSpan.fundamentalDomain Y.b) ≤ 1 := by
  classical
  have hr : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
    rw [Module.finrank_eq_card_basis Y.b, Fintype.card_fin]
  let b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι) :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℂ ι)).reindex (finCongr hr)
  rw [ZSpan.measure_fundamentalDomain Y.b volume b₀.toBasis]
  have h1 : volume (ZSpan.fundamentalDomain b₀.toBasis) = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀.toBasis volume),
      OrthonormalBasis.coe_toBasis, b₀.volume_parallelepiped]
  rw [h1, mul_one]
  calc ENNReal.ofReal |b₀.toBasis.det Y.b| ≤ ENNReal.ofReal 1 :=
        ENNReal.ofReal_le_ofReal (lemS_detM_le Y b₀)
    _ = 1 := ENNReal.ofReal_one

end

end ReciprocityTheory.ChartRestriction.G.I2

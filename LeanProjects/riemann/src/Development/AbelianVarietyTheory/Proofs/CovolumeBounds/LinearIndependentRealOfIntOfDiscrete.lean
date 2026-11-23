import Mathlib

open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix

namespace GlobalTheory

section Gram

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_gram_eq_normSq_det {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (b : OrthonormalBasis ι 𝕜 V) (v : ι → V) :
    (gram 𝕜 v).det = ((‖b.toBasis.det v‖ ^ 2 : ℝ) : 𝕜) := by
  have h : b.toBasis.det v = (Matrix.of fun i j ↦ b.repr (v j) i).det := by
    rw [Basis.det_apply]; congr 1
  rw [gram_eq_conjTranspose_mul b v, det_mul, det_conjTranspose, h, RCLike.star_def,
    RCLike.conj_mul]
  push_cast; rfl

theorem det_gram_le_of_finrank_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V] (h : finrank 𝕜 V = Fintype.card ι) (v : ι → V) :
    (gram 𝕜 v).det ≤ ((∏ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) := by
  let e := (Fintype.equivFin ι).symm
  have h' : finrank 𝕜 V = Fintype.card (Fin (Fintype.card ι)) := by simpa using h
  have h1 : (gram 𝕜 v).det = (gram 𝕜 (v ∘ e)).det := by
    rw [← det_submatrix_equiv_self e]; rfl
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h' (v ∘ e)
  have hb : b.toBasis.det (v ∘ e) = ∏ i, ⟪b i, (v ∘ e) i⟫_𝕜 :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det h' _
  rw [h1, det_gram_eq_normSq_det b, hb, RCLike.ofReal_le_ofReal, norm_prod, ← Finset.prod_pow,
    ← e.prod_comp (fun i ↦ ‖v i‖ ^ 2)]
  refine Finset.prod_le_prod (fun i _ ↦ by positivity) fun i _ ↦ ?_
  gcongr
  simpa using norm_inner_le_norm (𝕜 := 𝕜) (b i) (v (e i))

theorem norm_det_sq_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖A i j‖ ^ 2 := by
  let v : ι → EuclideanSpace 𝕜 ι := fun j ↦ WithLp.toLp 2 fun i ↦ A i j
  have h := det_gram_le_of_finrank_eq (𝕜 := 𝕜) (by simp) v
  rw [det_gram_eq_normSq_det (EuclideanSpace.basisFun ι 𝕜), RCLike.ofReal_le_ofReal] at h
  have h2 : (EuclideanSpace.basisFun ι 𝕜).toBasis.det v = A.det := by
    rw [Basis.det_apply]; congr 1
  rw [h2] at h
  refine h.trans_eq (Finset.prod_congr rfl fun j _ ↦ ?_)
  rw [EuclideanSpace.norm_sq_eq]

theorem posSemidef_det_le_prod_diag {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    A.det ≤ ∏ i, A i i := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.nonneg
  have h := norm_det_sq_le_prod_col B
  rw [← RCLike.ofReal_le_ofReal (K := 𝕜)] at h
  convert h using 1
  · rw [det_mul, star_eq_conjTranspose, det_conjTranspose, RCLike.star_def, RCLike.conj_mul]
    push_cast; rfl
  · push_cast
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    simp [mul_apply, RCLike.conj_mul]

theorem posSemidef_re_det_le_prod_diag {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    RCLike.re A.det ≤ ∏ i, RCLike.re (A i i) := by
  have h := posSemidef_det_le_prod_diag hA
  have h2 : ∏ i, A i i = ((∏ i, RCLike.re (A i i) : ℝ) : 𝕜) := by
    push_cast
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    exact (hA.isHermitian.coe_re_apply_self i).symm
  rw [h2] at h
  simpa only [RCLike.ofReal_re] using (RCLike.le_iff_re_im.1 h).1

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace 𝕜 V]

end Gram

section Covolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

theorem linearIndependent_real_of_int_of_discrete {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (L : Submodule ℤ F) [DiscreteTopology L]
    {v : ι → F} (hv : ∀ i, v i ∈ L) (hli : LinearIndependent ℤ v) : LinearIndependent ℝ v := by
  have hle : span ℤ (Set.range v) ≤ L := span_le.2 (Set.range_subset_iff.2 hv)
  have hd : DiscreteTopology (span ℤ (Set.range v)) :=
    DiscreteTopology.of_continuous_injective (β := L) (f := Set.inclusion hle)
      (continuous_inclusion hle) (Set.inclusion_injective hle)
  rw [linearIndependent_iff_card_eq_finrank_span] at hli ⊢
  rw [Real.finrank_eq_int_finrank_of_discrete hd, hli]

variable [MeasurableSpace E] [BorelSpace E]

theorem covolume_span_basis_eq_sqrt_det_gram [DecidableEq ι] (b : Basis ι ℝ E) :
    ZLattice.covolume (span ℤ (Set.range b)) = √(gram ℝ b).det := by
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm).symm
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    det_gram_eq_normSq_det o, measureReal_def, o.coe_toBasis, o.volume_parallelepiped]
  simp [Real.sqrt_sq_eq_abs]

theorem covolume_eq_sqrt_det_gram [DecidableEq ι] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    ZLattice.covolume L = √(gram ℝ fun i ↦ (b i : E)).det := by
  have h := covolume_span_basis_eq_sqrt_det_gram (b.ofZLatticeBasis ℝ L)
  rw [b.ofZLatticeBasis_span ℝ] at h
  rw [h]
  congr 3
  ext i
  simp

end Covolume

end GlobalTheory

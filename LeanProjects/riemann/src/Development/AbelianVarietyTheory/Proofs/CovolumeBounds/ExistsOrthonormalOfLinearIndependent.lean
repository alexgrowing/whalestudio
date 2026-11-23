import Mathlib

open Matrix Module
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.Hadamard

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem norm_orthonormalBasis_det_le (b : OrthonormalBasis ι 𝕜 E) (x : ι → E) :
    ‖b.toBasis.det x‖ ≤ ∏ k, ‖x k‖ := by
  classical
  haveI : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  letI : LocallyFiniteOrderBot ι :=
    LocallyFiniteOrderBot.ofIic ι (fun a => Finset.univ.filter (· ≤ a)) (by simp)
  have h : finrank 𝕜 E = Fintype.card ι := finrank_eq_card_basis b.toBasis
  set c := InnerProductSpace.gramSchmidtOrthonormalBasis h x with hc
  have h1 : b.toBasis.det x = b.toBasis.det c * c.toBasis.det x := by
    conv_lhs => rw [b.toBasis.det.eq_smul_basis_det c.toBasis]
    simp
  have h2 : c.toBasis.det x = ∏ i, ⟪c i, x i⟫_𝕜 := by
    convert InnerProductSpace.gramSchmidtOrthonormalBasis_det h x
  rw [h1, norm_mul, b.det_to_matrix_orthonormalBasis c, one_mul, h2, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
  simpa [c.orthonormal.1 i] using norm_inner_le_norm (𝕜 := 𝕜) (c i) (x i)

theorem norm_det_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ j, √(∑ i, ‖A i j‖ ^ 2) := by
  have h := norm_orthonormalBasis_det_le (EuclideanSpace.basisFun ι 𝕜)
    (fun j => (WithLp.toLp 2 fun i => A i j : EuclideanSpace 𝕜 ι))
  simp only [EuclideanSpace.norm_eq] at h
  convert h using 2
  rw [Basis.det_apply]
  congr 1

theorem norm_det_le_prod_row (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ i, √(∑ j, ‖A i j‖ ^ 2) := by
  rw [← det_transpose]
  exact norm_det_le_prod_col Aᵀ

theorem norm_det_sq_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖A i j‖ ^ 2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_prod_col A) 2).trans_eq ?_
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun j _ => Real.sq_sqrt (by positivity)

theorem norm_det_sq_le_prod_row (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [← det_transpose]
  exact norm_det_sq_le_prod_col Aᵀ

theorem det_gram_nonneg (x : ι → E) : 0 ≤ (gram 𝕜 x).det :=
  (posSemidef_gram 𝕜 x).det_nonneg

theorem re_det_gram_nonneg (x : ι → E) : 0 ≤ RCLike.re (gram 𝕜 x).det :=
  (RCLike.nonneg_iff.mp (det_gram_nonneg x)).1

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in

theorem gram_sum_smul [Fintype κ] (e : ι → E) (m : Matrix ι κ 𝕜) :
    gram 𝕜 (fun j => ∑ i, m i j • e i) = mᴴ * gram 𝕜 e * m := by
  ext j k
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_apply,
    conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem re_det_gram_sum_smul (e : ι → E) (m : Matrix ι ι 𝕜) :
    RCLike.re (gram 𝕜 (fun j => ∑ i, m i j • e i)).det
      = ‖m.det‖ ^ 2 * RCLike.re (gram 𝕜 e).det := by
  rw [gram_sum_smul, det_mul, det_mul, det_conjTranspose, mul_right_comm, RCLike.star_def,
    RCLike.conj_mul]
  norm_cast
  rw [RCLike.re_ofReal_mul]

theorem exists_orthonormal_of_linearIndependent {x : ι → E} (hx : LinearIndependent 𝕜 x) :
    ∃ (e : ι → E) (m : Matrix ι ι 𝕜), Orthonormal 𝕜 e ∧ ∀ j, x j = ∑ i, m i j • e i := by
  set S := Submodule.span 𝕜 (Set.range x)
  haveI : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range x)
  have h : finrank 𝕜 S = Fintype.card ι := finrank_span_eq_card hx
  let b : OrthonormalBasis ι 𝕜 S :=
    (stdOrthonormalBasis 𝕜 S).reindex (Fintype.equivFinOfCardEq h.symm).symm
  let y : ι → S := fun j => ⟨x j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨fun i => (b i : E), of fun i j => b.repr (y j) i,
    b.orthonormal.comp_linearIsometry S.subtypeₗᵢ, fun j => ?_⟩
  have := congrArg (fun s : S => (s : E)) (b.sum_repr (y j))
  simpa using this.symm

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem norm_sum_smul_sq {e : ι → E} (he : Orthonormal 𝕜 e) (c : ι → 𝕜) :
    ‖∑ i, c i • e i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  have h := he.inner_sum c c Finset.univ
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [RCLike.conj_mul] at h
  exact_mod_cast h

theorem re_det_gram_le_prod (x : ι → E) : RCLike.re (gram 𝕜 x).det ≤ ∏ k, ‖x k‖ ^ 2 := by
  by_cases hx : LinearIndependent 𝕜 x
  · obtain ⟨e, m, he, hm⟩ := exists_orthonormal_of_linearIndependent hx
    obtain rfl : x = fun j => ∑ i, m i j • e i := funext hm
    rw [re_det_gram_sum_smul, gram_eq_one_iff_orthonormal.mpr he]
    simp only [det_one, RCLike.one_re, mul_one, norm_sum_smul_sq he]
    exact norm_det_sq_le_prod_col m
  · rw [← det_gram_ne_zero_iff_linearIndependent, not_not] at hx
    rw [hx, map_zero]
    positivity

omit [DecidableEq ι] in

theorem det_gram_comp_equiv [DecidableEq ι] (x : ι → E) (σ : κ ≃ ι) :
    (gram 𝕜 (x ∘ σ)).det = (gram 𝕜 x).det :=
  det_submatrix_equiv_self σ (gram 𝕜 x)

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in

theorem sum_norm_apply_sq_le {e : ι → E} (he : Orthonormal 𝕜 e) (φ : E →L[𝕜] 𝕜) :
    ∑ i, ‖φ (e i)‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
  set s := ∑ i, ‖φ (e i)‖ ^ 2 with hs
  set v := ∑ i, (starRingEnd 𝕜) (φ (e i)) • e i with hv
  have hs0 : 0 ≤ s := by positivity
  have h1 : ‖v‖ ^ 2 = s := by simp [hv, norm_sum_smul_sq he, hs]
  have h2 : φ v = (s : 𝕜) := by
    simp [hv, hs, RCLike.conj_mul]
  have h3 : s ≤ ‖φ‖ * ‖v‖ := by
    have := φ.le_opNorm v
    rwa [h2, RCLike.norm_ofReal, abs_of_nonneg hs0] at this
  nlinarith [sq_nonneg (‖φ‖ - ‖v‖)]

theorem norm_det_apply_sq_le (φ : ι → E →L[𝕜] 𝕜) (x : ι → E) :
    ‖(of fun j k => φ j (x k)).det‖ ^ 2 ≤ RCLike.re (gram 𝕜 x).det * ∏ j, ‖φ j‖ ^ 2 := by
  by_cases hx : LinearIndependent 𝕜 x
  · obtain ⟨e, m, he, hm⟩ := exists_orthonormal_of_linearIndependent hx
    have h : (of fun j k => φ j (x k)) = (of fun j i => φ j (e i)) * m := by
      ext j k
      simp [hm, mul_apply, mul_comm]
    rw [h]
    obtain rfl : x = fun j => ∑ i, m i j • e i := funext hm
    rw [re_det_gram_sum_smul, gram_eq_one_iff_orthonormal.mpr he, det_mul, norm_mul, mul_pow,
      det_one, RCLike.one_re, mul_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ((norm_det_sq_le_prod_row _).trans ?_) (by positivity)
    exact Finset.prod_le_prod (fun _ _ => by positivity) fun j _ => sum_norm_apply_sq_le he (φ j)
  · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hx
    have h0 : (of fun j k => φ j (x k)).det = 0 := by
      refine exists_mulVec_eq_zero_iff.mp ⟨g, fun h => hi (congrFun h i), ?_⟩
      funext j
      have := congrArg (φ j) hg
      simpa [mulVec, dotProduct, mul_comm] using this
    rw [h0, norm_zero]
    exact (by norm_num : (0 : ℝ) ^ 2 ≤ 0).trans
      (mul_nonneg (re_det_gram_nonneg x) (by positivity))

theorem norm_det_apply_le (φ : ι → E →L[𝕜] 𝕜) (x : ι → E) :
    ‖(of fun j k => φ j (x k)).det‖ ≤ (∏ k, ‖x k‖) * ∏ j, ‖φ j‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
  exact (norm_det_apply_sq_le φ x).trans
    (mul_le_mul_of_nonneg_right (re_det_gram_le_prod x) (by positivity))

end GlobalTheory.Hadamard

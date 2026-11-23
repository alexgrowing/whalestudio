import Mathlib
import Formalism.HyperbolicPlaceProducts.Statement
import Formalism.GelfandTransference.HadamardGelfand.Hadamard

open Matrix Finset ComplexConjugate

noncomputable section

namespace Formalism.SLP.P

variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]

lemma row_sq_le (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) (c : ℝ) (hB : ∀ x y, ‖B x y‖ ≤ c * ‖x‖ * ‖y‖)
    {m : ℕ} (x : V₁) (hx : ‖x‖ = 1) (f : Fin m → V₂) (hf : Orthonormal ℂ f) :
    ∑ l, ‖B x (f l)‖ ^ 2 ≤ c ^ 2 := by
  set a : Fin m → ℂ := fun l => B x (f l) with ha
  set y : V₂ := ∑ l, a l • f l with hy
  set S : ℝ := ∑ l, ‖a l‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun l _ => by positivity
  have h1 : B x y = (S : ℂ) := by
    rw [hy, map_sum, hS]
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, Complex.conj_mul']
  have h2 : ‖y‖ ^ 2 = S := by
    rw [@norm_sq_eq_re_inner ℂ, hy, hf.inner_sum, hS, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.conj_mul']
    norm_cast
  have h3 : S ≤ c * ‖y‖ := by
    have := hB x y
    rw [h1, hx, mul_one, Complex.norm_real, Real.norm_of_nonneg hS0] at this
    exact this
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · have h4 : S * S ≤ c ^ 2 * S := by
      have h5 : 0 ≤ c * ‖y‖ := le_trans hS0 h3
      calc S * S ≤ (c * ‖y‖) * (c * ‖y‖) := mul_le_mul h3 h3 hS0 h5
        _ = c ^ 2 * S := by rw [← h2]; ring
    exact le_of_mul_le_mul_right h4 h0

lemma det_orth_sq_le (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) (c : ℝ) (hB : ∀ x y, ‖B x y‖ ≤ c * ‖x‖ * ‖y‖)
    {m : ℕ} (e : Fin m → V₁) (he : Orthonormal ℂ e) (f : Fin m → V₂) (hf : Orthonormal ℂ f) :
    ‖(Matrix.of fun k l => B (e k) (f l)).det‖ ^ 2 ≤ c ^ (2 * m) := by
  refine le_trans (Formalism.HadamardInequality.P.hadamard_inequality_holds m _) ?_
  calc ∏ k, ∑ l, ‖(Matrix.of fun k l => B (e k) (f l)) k l‖ ^ 2 ≤ ∏ _k : Fin m, c ^ 2 :=
        Finset.prod_le_prod (fun k _ => Finset.sum_nonneg fun l _ => by positivity)
          fun k _ => row_sq_le B c hB (e k) (he.1 k) f hf
    _ = c ^ (2 * m) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]

lemma exists_orth_decomp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {m : ℕ}
    (u : Fin m → V) (hu : LinearIndependent ℂ u) :
    ∃ (e : Fin m → V) (A : Matrix (Fin m) (Fin m) ℂ),
      Orthonormal ℂ e ∧ ∀ i, u i = ∑ k, A i k • e k := by
  have h : ∀ i, ∃ g : Fin m → ℂ, ∑ k, g k • InnerProductSpace.gramSchmidtNormed ℂ u k = u i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1
      (by rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt]; exact Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨InnerProductSpace.gramSchmidtNormed ℂ u, fun i k => (h i).choose k,
    InnerProductSpace.gramSchmidtNormed_orthonormal hu, fun i => (h i).choose_spec.symm⟩

lemma gram_eq_of_decomp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {m : ℕ}
    (e : Fin m → V) (he : Orthonormal ℂ e) (A : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → V)
    (hu : ∀ i, u i = ∑ k, A i k • e k) :
    Matrix.gram ℂ u = (A * Aᴴ)ᵀ := by
  ext i j
  rw [Matrix.gram_apply, hu i, hu j, he.inner_sum, Matrix.transpose_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, mul_comm]
  rfl

lemma norm_det_gram_of_decomp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {m : ℕ}
    (e : Fin m → V) (he : Orthonormal ℂ e) (A : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → V)
    (hu : ∀ i, u i = ∑ k, A i k • e k) :
    ‖(Matrix.gram ℂ u).det‖ = ‖A.det‖ ^ 2 := by
  rw [gram_eq_of_decomp e he A u hu, Matrix.det_transpose, Matrix.det_mul, Matrix.det_conjTranspose,
    norm_mul, norm_star, sq]

lemma bmat_eq_of_decomp (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) {m : ℕ} (e : Fin m → V₁) (f : Fin m → V₂)
    (A C : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → V₁) (w : Fin m → V₂)
    (hu : ∀ i, u i = ∑ k, A i k • e k) (hw : ∀ j, w j = ∑ l, C j l • f l) :
    (Matrix.of fun i j => B (u i) (w j)) = A * (Matrix.of fun k l => B (e k) (f l)) * Cᴴ := by
  ext i j
  rw [Matrix.of_apply, hu i, hw j, Matrix.mul_apply]
  simp only [map_sum, LinearMap.map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem sesquilinear_determinant_holds : Formalism.SLP.SesqDet := by
  intro V₁ V₂ _ _ _ _ B c hB m u w
  have hc : 0 ≤ c ^ (2 * m) := by rw [pow_mul]; positivity
  by_cases hu : LinearIndependent ℂ u
  · by_cases hw : LinearIndependent ℂ w
    · obtain ⟨e, A, he, hA⟩ := exists_orth_decomp u hu
      obtain ⟨f, C, hf, hC⟩ := exists_orth_decomp w hw
      rw [bmat_eq_of_decomp B e f A C u w hA hC, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
        norm_det_gram_of_decomp e he A u hA, norm_det_gram_of_decomp f hf C w hC, norm_mul, norm_mul, norm_star]
      have h1 := det_orth_sq_le B c hB e he f hf
      calc (‖A.det‖ * ‖(Matrix.of fun k l => B (e k) (f l)).det‖ * ‖C.det‖) ^ 2
          = ‖A.det‖ ^ 2 * ‖(Matrix.of fun k l => B (e k) (f l)).det‖ ^ 2 * ‖C.det‖ ^ 2 := by ring
        _ ≤ ‖A.det‖ ^ 2 * c ^ (2 * m) * ‖C.det‖ ^ 2 := by gcongr
        _ = c ^ (2 * m) * ‖A.det‖ ^ 2 * ‖C.det‖ ^ 2 := by ring
    · obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hw
      have hdet : (Matrix.of fun i j => B (u i) (w j)).det = 0 := by
        refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨fun j => star (g j), fun h0 => hi0 ?_, ?_⟩
        · have := congrFun h0 i0
          simpa using this
        · ext i
          simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
          have := congrArg (B (u i)) hg
          simp only [map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, map_zero, starRingEnd_apply] at this
          rw [← this]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [hdet, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  · obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hu
    have hdet : (Matrix.of fun i j => B (u i) (w j)).det = 0 := by
      refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨g, fun h0 => hi0 (congrFun h0 i0), ?_⟩
      ext j
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      have := congrArg (fun x => B x (w j)) hg
      simp only [map_sum, LinearMap.map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        map_zero, LinearMap.zero_apply] at this
      exact this
    rw [hdet, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

end Formalism.SLP.P

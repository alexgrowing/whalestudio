import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs

noncomputable section

open Matrix InnerProductSpace
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {n m : ℕ}

def gram (w : Fin m → EuclideanSpace ℂ (Fin n)) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => inner ℂ (w a) (w b)

theorem gram_comb (w : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ) :
    gram (fun a => ∑ b, τ b a • w b) = τᴴ * gram w * τ := by
  ext a b
  simp only [gram, of_apply, mul_apply, conjTranspose_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  simp only [starRingEnd_apply]; ring

theorem gs_fac (w : Fin m → EuclideanSpace ℂ (Fin n)) (hw : LinearIndependent ℂ w) :
    ∃ (u : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ), Orthonormal ℂ u ∧
      τ.BlockTriangular id ∧ (∀ j, τ j j ≠ 0) ∧ (∀ a, w a = ∑ b, τ b a • u b) ∧
      ∀ a, u a ∈ Submodule.span ℂ (Set.range w) := by
  set u := gramSchmidtNormed ℂ w with hudef
  have hu : Orthonormal ℂ u := gramSchmidtNormed_orthonormal hw
  have hspan : Submodule.span ℂ (Set.range u) = Submodule.span ℂ (Set.range w) := by
    rw [hudef, span_gramSchmidtNormed_range, span_gramSchmidt]
  refine ⟨u, fun b a => inner ℂ (u b) (w a), hu, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hij' : j < i := hij
    simp only [hudef, gramSchmidtNormed, inner_smul_left]
    rw [gramSchmidt_inv_triangular ℂ w hij', mul_zero]
  · intro j hj
    have hg := gramSchmidt_ne_zero j hw
    have h0 : inner ℂ (u j) (w j) = inner ℂ (u j) (gramSchmidt ℂ w j) := by
      conv_lhs => rw [gramSchmidt_def'' ℂ w j]
      rw [inner_add_right, inner_sum, Finset.sum_eq_zero, add_zero]
      intro i hi
      rw [inner_smul_right]
      simp only [hudef, gramSchmidtNormed, inner_smul_left,
        gramSchmidt_orthogonal ℂ w (Finset.mem_Iio.1 hi).ne', mul_zero]
    simp only at hj
    rw [h0] at hj
    simp only [hudef, gramSchmidtNormed, inner_smul_left, inner_self_eq_norm_sq_to_K] at hj
    simp [hg] at hj
  · intro a
    have : w a ∈ Submodule.span ℂ (Set.range u) := hspan ▸ Submodule.subset_span ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 this
    conv_lhs => rw [← hc]
    refine Finset.sum_congr rfl fun b _ => ?_
    show c b • u b = inner ℂ (u b) (w a) • u b
    rw [← hc, hu.inner_right_fintype]
  · intro a; rw [← hspan]; exact Submodule.subset_span ⟨a, rfl⟩

theorem det_gram_of (w u : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ)
    (hu : Orthonormal ℂ u) (hτ : τ.BlockTriangular id) (hw : ∀ a, w a = ∑ b, τ b a • u b) :
    (gram w).det = ((∏ j, ‖τ j j‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : gram u = 1 := by
    ext i j; simp [gram, orthonormal_iff_ite.1 hu, Matrix.one_apply]
  have hg : gram w = τᴴ * τ := by
    rw [show w = fun a => ∑ b, τ b a • u b from funext hw, gram_comb, h1, Matrix.mul_one]
  rw [hg, det_mul, det_conjTranspose, det_of_isUpperTriangular hτ]
  rw [show star (∏ j, τ j j) = ∏ j, star (τ j j) by
    simpa using map_prod (starRingEnd ℂ) (fun j => τ j j) Finset.univ]
  rw [← Finset.prod_mul_distrib, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← starRingEnd_apply, Complex.conj_mul']; push_cast; ring

theorem ga_eq (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l Y = (gram (fun a : Fin (l.val + 1) =>
      (WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1))))).det.re := by
  unfold Ga; congr 2; ext a b
  simp only [gram, of_apply, EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]

theorem linInd_toLp {ι : Type*} (Y : ι → Fin n → ℂ) (hY : LinearIndependent ℂ Y) :
    LinearIndependent ℂ (fun a => (WithLp.toLp 2 (Y a) : EuclideanSpace ℂ (Fin n))) :=
  hY.map' (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap (LinearEquiv.ker _)

theorem ga_pos (k r : ℕ) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (hY : LinearIndependent ℂ Y)
    (l : Fin (r + 1)) : 0 < Ga k r l Y := by
  rw [ga_eq]
  have hw := (linInd_toLp Y hY).comp _ (Fin.castLE_injective (show l.val + 1 ≤ r + 1 by omega))
  obtain ⟨u, τ, hu, hτ, hd, hwe, -⟩ := gs_fac (fun a : Fin (l.val + 1) =>
    (WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) hw
  rw [det_gram_of _ u τ hu hτ hwe, Complex.ofReal_re]
  exact Finset.prod_pos fun j _ => pow_pos (norm_pos_iff.2 (hd j)) 2

theorem norm_mulVec_le {k r : ℕ} (A : Mat k r) (y : Fin (2 * r + k + 1) → ℂ) :
    ‖(WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))‖ ≤
      gN A * ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin (2 * r + k + 1)))‖ := by
  have hnn : (0 : ℝ) ≤ ∑ i, ∑ j, Complex.normSq (A i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (A i j)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, gN, ← Real.sqrt_mul hnn]
  refine Real.sqrt_le_sqrt ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(A *ᵥ y) i‖ ≤ ∑ j, ‖A i j‖ * ‖y j‖ := by
    simp only [mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  calc ‖(A *ᵥ y) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖y j‖) ^ 2 := by gcongr
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖y j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = ∑ j, Complex.normSq (A i j) * ∑ j, ‖y j‖ ^ 2 := by
      rw [← Finset.sum_mul]; simp only [Complex.normSq_eq_norm_sq]

end ReciprocityTheory.ChartRestriction.DS.Xi.GS

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
open GlobalTheory.LocFinIso

namespace GlobalTheory.LeftMulRep
open Matrix

theorem toEuclideanCLM_continuous (n : ℕ) :
    Continuous (toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) := by
  let f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun M => toEuclideanCLM (n := Fin n) (𝕜 := ℂ) M
      map_add' := fun M N => map_add _ M N
      map_smul' := fun c M => by simp }
  exact f.continuous_of_finiteDimensional

theorem norm_toEuclideanCLM_unitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    ‖toEuclideanCLM (n := Fin n) (𝕜 := ℂ) U v‖ = ‖v‖ := by
  have hg : star U * U = 1 := hU.1
  revert v
  rw [ContinuousLinearMap.norm_map_iff_adjoint_comp_self, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star, ← ContinuousLinearMap.mul_def, ← map_mul, hg, map_one]

theorem leftMul_spec :
  ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Set G) (m : ℕ) (A : G → Matrix (Fin m) (Fin m) ℂ), A 1 = 1 → (∀ k ∈ K, ∀ k' ∈ K, A (k * k') = A k * A k') → (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ) → ContinuousOn A K → leftMul A 1 = 1 ∧ (∀ k ∈ K, ∀ k' ∈ K, leftMul A (k * k') = leftMul A k * leftMul A k') ∧ (∀ k ∈ K, ∀ v, ‖leftMul A k v‖ = ‖v‖) ∧ ∀ v, ContinuousOn (fun k => leftMul A k v) K := by
  intro G _ _ K m A h1 hmul hU hc
  have hB : ∀ g, leftMul A g = toEuclideanCLM (n := Fin (m * m)) (𝕜 := ℂ)
      (reindexAlgEquiv ℂ ℂ finProdFinEquiv (kroneckerMap (· * ·) (A g) (1 : Matrix (Fin m) (Fin m) ℂ))) := fun g => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hB, h1]
    have : kroneckerMap (· * ·) (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) = 1 :=
      Matrix.one_kronecker_one
    rw [this, map_one, map_one]
  · intro k hk k' hk'
    rw [hB, hB, hB, hmul k hk k' hk', ← map_mul, ← map_mul]
    congr 2
    have := Matrix.mul_kronecker_mul (A k) (A k') (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ)
    rw [Matrix.mul_one] at this
    exact this
  · intro k hk v
    apply norm_toEuclideanCLM_unitary
    have h1u : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ unitary (Matrix (Fin m) (Fin m) ℂ) := one_mem _
    have hk2 := Matrix.kronecker_mem_unitary (hU k hk) h1u
    rw [reindex_apply]
    constructor
    · rw [star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv, ← star_eq_conjTranspose, hk2.1,
        submatrix_one_equiv]
    · rw [star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv, ← star_eq_conjTranspose, hk2.2,
        submatrix_one_equiv]
  · intro v
    have hev : Continuous (fun T : EuclideanSpace ℂ (Fin (m * m)) →L[ℂ] EuclideanSpace ℂ (Fin (m * m)) => T v) :=
      (ContinuousLinearMap.apply ℂ _ v).continuous
    have hk : ContinuousOn (fun k => kroneckerMap (· * ·) (A k) (1 : Matrix (Fin m) (Fin m) ℂ)) K :=
      by
        have hkc : Continuous (fun M : Matrix (Fin m) (Fin m) ℂ =>
            kroneckerMap (· * ·) M (1 : Matrix (Fin m) (Fin m) ℂ)) :=
          continuous_matrix fun i j => by
            simp only [kroneckerMap_apply]
            exact (continuous_id.matrix_elem i.1 j.1).mul continuous_const
        exact hkc.comp_continuousOn hc
    have hr := (continuous_id.matrix_reindex finProdFinEquiv finProdFinEquiv).comp_continuousOn hk
    exact hev.comp_continuousOn ((toEuclideanCLM_continuous (m * m)).comp_continuousOn hr)

end GlobalTheory.LeftMulRep

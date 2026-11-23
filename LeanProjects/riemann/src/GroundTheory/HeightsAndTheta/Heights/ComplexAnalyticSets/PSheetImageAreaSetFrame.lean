import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAreaMultiplicity
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGraphAreaHolomorphic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

namespace SheetImageAreaSet

theorem exists_adapted_frame {n d : ℕ}
    (P : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) (hP : Function.Surjective P) :
    ∃ (m : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m)
      (Q : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
      (L : EuclideanSpace ℂ (Fin d) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d))
      (π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)),
      (∀ z, ‖Q z‖ = ‖z‖) ∧
        ∀ z, Q z = WithLp.toLp 2 (fun j => Sum.elim (fun i => L (P z) i) (fun i => π z i) (e j)) := by
  classical
  set K := LinearMap.ker P with hKdef
  have h1 := K.finrank_add_finrank_orthogonal
  have h2 := LinearMap.finrank_range_add_finrank_ker P
  rw [LinearMap.range_eq_top.2 hP, finrank_top] at h2
  simp only [finrank_euclideanSpace_fin] at h1 h2
  rw [← hKdef] at h2
  have hW : finrank ℂ Kᗮ = d := by omega
  have hn : n = d + finrank ℂ K := by omega
  let bW : OrthonormalBasis (Fin d) ℂ Kᗮ := (stdOrthonormalBasis ℂ Kᗮ).reindex (finCongr hW)
  let bK := stdOrthonormalBasis ℂ K
  let e : Fin n ≃ Fin d ⊕ Fin (finrank ℂ K) := (finCongr hn).trans finSumFinEquiv.symm
  let πW : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
    bW.repr.toLinearMap ∘ₗ (Kᗮ.orthogonalProjectionOnto : _ →L[ℂ] Kᗮ).toLinearMap
  let π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ K)) :=
    bK.repr.toLinearMap ∘ₗ (K.orthogonalProjectionOnto : _ →L[ℂ] K).toLinearMap
  obtain ⟨R, hR⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)
  have hPR : ∀ y, P (R y) = y := fun y => LinearMap.congr_fun hR y
  have hWR : ∀ z, πW (R (P z)) = πW z := by
    intro z
    have hmem : R (P z) - z ∈ Kᗮᗮ :=
      K.le_orthogonal_orthogonal (by simp [hKdef, LinearMap.mem_ker, hPR])
    have h0 := Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hmem
    have h3 : πW (R (P z) - z) = 0 := by simp [πW, h0]
    rwa [map_sub, sub_eq_zero] at h3
  have hinj : Function.Injective (πW ∘ₗ R) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : Kᗮ.orthogonalProjectionOnto (R y) = 0 := by simpa [πW] using hy
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, K.orthogonal_orthogonal] at h0
    rw [← hPR y]
    exact h0
  let L := LinearEquiv.ofInjectiveEndo _ hinj
  let Q : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toFun := fun z => WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j))
      map_add' := fun z w => by
        ext j
        obtain ⟨s, rfl⟩ := e.symm.surjective j
        rcases s with i | i <;> simp
      map_smul' := fun c z => by
        ext j
        obtain ⟨s, rfl⟩ := e.symm.surjective j
        rcases s with i | i <;> simp }
  refine ⟨finrank ℂ K, e, Q, L, π, fun z => ?_, fun z => ?_⟩
  · refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    show ‖(WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j)) :
      EuclideanSpace ℂ (Fin n))‖ ^ 2 = _
    rw [GraphAreaHolomorphic.norm_sq_sumElim e (πW z) (π z), Submodule.norm_sq_eq_add_norm_sq_projection z K,
      add_comm]
    simp [πW, π]
  · show WithLp.toLp 2 (fun j => Sum.elim (fun i => πW z i) (fun i => π z i) (e j)) = _
    simp [L, hWR]

theorem areaJacobian_eq_normDet {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) : areaJacobian M = M.normDet := by
  have h := M.normDet_sq
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [areaJacobian, ← h, Real.sqrt_sq M.normDet_nonneg]

theorem areaJacobian_comp_of_norm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (Q : F →ₗ[ℝ] F) (hQ : ∀ v, ‖Q v‖ = ‖v‖) (M : E →ₗ[ℝ] F) :
    areaJacobian (Q ∘ₗ M) = areaJacobian M := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp,
    show (Q.domRestrict (LinearMap.range M)).normDet = 1 from
      LinearIsometry.normDet_eq_one ⟨Q.domRestrict _, fun v => hQ v⟩, one_mul]

theorem areaJacobian_comp_endo {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) (T : E →ₗ[ℝ] E) :
    areaJacobian (M ∘ₗ T) = areaJacobian M * |LinearMap.det T| := by
  rw [areaJacobian_eq_normDet, areaJacobian_eq_normDet, LinearMap.normDet_comp_of_finrank_eq _ _ rfl,
    LinearMap.normDet_eq_abs_det]

end SheetImageAreaSet

end

end GroundTheory.Heights₂.Heights

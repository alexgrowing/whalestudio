import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphJacContinuous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open scoped InnerProductSpace

theorem det_one_add_adjoint_comp_self_pos {k m : ℕ}
    (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < LinearMap.det ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
      LinearMap.adjoint B ∘ₗ B) := by
  set S : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) := 1 + LinearMap.adjoint B ∘ₗ B
    with hSdef
  have hBB : (LinearMap.adjoint B ∘ₗ B).IsPositive := LinearMap.isPositive_adjoint_comp_self B
  have hS : S.IsPositive := LinearMap.isPositive_one.add hBB
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  rw [hS.isSymmetric.det_eq_prod_eigenvalues hn]
  refine Finset.prod_pos fun i _ => ?_
  set v := hS.isSymmetric.eigenvectorBasis hn i
  have hv : ‖v‖ = 1 := (hS.isSymmetric.eigenvectorBasis hn).orthonormal.1 i
  have h1 : ⟪S v, v⟫_ℝ = hS.isSymmetric.eigenvalues hn i := by
    rw [hS.isSymmetric.apply_eigenvectorBasis hn i]
    simp [real_inner_smul_left, hv, v]
  have h2 : ⟪S v, v⟫_ℝ = ‖v‖ ^ 2 + ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ := by
    rw [hSdef, LinearMap.add_apply, inner_add_left, Module.End.one_apply, real_inner_self_eq_norm_sq]
  have h3 : 0 ≤ ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ := by
    simpa using hBB.re_inner_nonneg_left v
  have : 0 < (hS.isSymmetric.eigenvalues hn i : ℝ) := by
    rw [← h1, h2, hv]; linarith
  simpa using this

theorem graphJac_pos {k m : ℕ} (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < graphJac B :=
  Real.sqrt_pos.mpr (det_one_add_adjoint_comp_self_pos B)

theorem continuous_graphJac (k m : ℕ) :
    Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  have hc : Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      (1 + (ContinuousLinearMap.adjoint B).comp B :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :=
    continuous_const.add ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)
  have heq : (fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) =
      fun B => √((1 + (ContinuousLinearMap.adjoint B).comp B :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)).det) := by
    funext B
    rfl
  rw [heq]
  exact (ContinuousLinearMap.continuous_det.comp hc).sqrt

theorem GraphJacContinuous.proof : GraphJacContinuous.Statement := by
  intro k m A ε hε
  set g := fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
    graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) with hg
  have hgA : 0 < g A := graphJac_pos _
  set η := ε * g A / (1 + ε) with hη
  have hη0 : 0 < η := by positivity
  have hηe : (1 + ε) * η = ε * g A := by rw [hη]; field_simp
  obtain ⟨δ, hδ, hδη⟩ := Metric.continuous_iff.mp (continuous_graphJac k m) A η hη0
  refine ⟨δ / 2, half_pos hδ, fun B hB => ?_⟩
  have hd : dist B A < δ := by rw [dist_eq_norm]; linarith
  have h := hδη B hd
  rw [Real.dist_eq, abs_lt] at h
  change g B ≤ (1 + ε) * g A ∧ g A ≤ (1 + ε) * g B
  constructor
  · nlinarith
  · nlinarith

end

end GroundTheory.Heights₂.Heights

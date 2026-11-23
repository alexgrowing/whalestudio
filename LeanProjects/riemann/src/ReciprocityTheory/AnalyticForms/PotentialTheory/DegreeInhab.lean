import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement

namespace ReciprocityTheory.AnForm.M

open FinHolAtlas

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoMap_id (A : FinHolAtlas e X) : HoloMap A A id :=
  ⟨continuous_id, fun j k => A.holo j k⟩

theorem isAnalyticSubset_empty (A : FinHolAtlas e X) : A.IsAnalyticSubset ∅ := by
  intro x
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ x, 1, fun _ _ => (1 : ℂ), ?_, ?_⟩
  · intro i j
    exact analyticOnNhd_const
  · ext y
    simp

theorem det_fderiv_transition_ne_zero (A : FinHolAtlas e X) (j k : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hk : (A.chart j).symm y ∈ (A.chart k).source) :
    LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
  have hyU : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := ⟨hy, hk⟩
  have hfd : DifferentiableAt ℂ (A.chart k ∘ (A.chart j).symm) y :=
    (A.holo j k y hyU).differentiableAt
  have hz : (A.chart k ∘ (A.chart j).symm) y ∈
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source := by
    refine ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k ((A.chart j).symm y)) ∈ (A.chart j).source
    rw [(A.chart k).left_inv hk]
    exact (A.chart j).map_target hy
  have hgd : DifferentiableAt ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y) :=
    (A.holo k j _ hz).differentiableAt
  have hev : (A.chart j ∘ (A.chart k).symm) ∘ (A.chart k ∘ (A.chart j).symm) =ᶠ[nhds y] id := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    show (A.chart j) ((A.chart k).symm ((A.chart k) ((A.chart j).symm y'))) = y'
    rw [(A.chart k).left_inv hy'.2, (A.chart j).right_inv hy'.1]
  have hcomp : (fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)).comp
      (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) = ContinuousLinearMap.id ℂ (Fin e → ℂ) := by
    rw [← fderiv_comp y hgd hfd, hev.fderiv_eq, fderiv_id]
  intro h0
  have hdet : LinearMap.det (((fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).comp
      ((fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) = 1 := by
    have hc : ((fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)).comp ((fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
        (((fderiv ℂ (A.chart j ∘ (A.chart k).symm) ((A.chart k ∘ (A.chart j).symm) y)).comp (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y) : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := rfl
    rw [hc, hcomp, ContinuousLinearMap.coe_id, LinearMap.det_id]
  rw [LinearMap.det_comp, h0, mul_zero] at hdet
  exact zero_ne_one hdet

theorem isDegreeOff_id (A : FinHolAtlas e X) : IsDegreeOff A A id 1 ∅ := by
  refine ⟨isAnalyticSubset_empty A, interior_empty, ?_, ?_, ?_, ?_⟩
  · rw [Set.preimage_id]
    exact isAnalyticSubset_empty A
  · rw [Set.preimage_id]
    exact interior_empty
  · intro x _
    rw [Set.preimage_id]
    exact Set.ncard_singleton x
  · intro j k y hy _ hk
    rw [Function.id_comp]
    exact det_fderiv_transition_ne_zero A j k hy hk

end ReciprocityTheory.AnForm.M

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterChart
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMax
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterMemIff
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSuppLemmas
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G OrbitChartMax

theorem OrbitCenterChart.proof : OrbitCenterChart.Statement := by
  classical
  intro ι _ _ _ n A x s hx hs V hV c hc v
  obtain ⟨hVmin, -⟩ := hV
  have : V.IsPrime := hVmin.1.1
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  obtain ⟨a, -, hsa, -⟩ := hs
  have hsa' : IsWeightedHomogeneous (coordDeg n) s a := (geoMultiHomog_iff s a).mp hsa

  have hVh : ∀ f ∈ V, ∀ b, weightedHomogeneousComponent (coordDeg n) b f ∈ V := by
    have hJ : NumbersDVR.IsMultiHomogIdeal (ι := blockIdx n) (orbitIdeal x ⊔ Ideal.span {s}) := by
      intro f hf b
      obtain ⟨p, hp, t, ht, rfl⟩ := Submodule.mem_sup.mp hf
      rw [map_add]
      exact Submodule.add_mem_sup (OrbitCurve.weightedHomogeneousComponent_mem_orbitIdeal x hp b)
        (NumbersDVR.isMultiHomogIdeal_span_singleton (e := a) hsa' t ht b)
    exact NumbersDVR.MinimalPrimeMultiHomog.proof ℤ ι (blockIdx n) _ V hJ hVmin

  have hxc : ∀ k, flatCone x ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    refine hc k (hPV ?_)
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [h0]
  have hyc : ∀ k, genPt V ⟨k, c k⟩ ≠ 0 := fun k ↦ genPt_ne_zero V (hc k)

  have hVzero : ∀ f ∈ V, aeval (dehomCoords (genPt V) c) f = 0 := by
    intro f hf
    rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    exact (aeval_dehomCoords_of_homog (genPt V) c
      (weightedHomogeneousComponent_isWeightedHomogeneous b f)).trans
      (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr (hVh f hf b)) _)
  have hker : ∀ F, chartEval x c F = 0 → aeval (dehomCoords (genPt V) c) F = 0 := by
    intro F hF
    rw [chartEval_eq_zero_iff] at hF
    have hF' := (aeval_dehomCoords (flatCone x) c hxc F).symm.trans hF
    have hH := (mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hxc _)
    have hHV : homogenize c F ∈ V :=
      hPV (mem_orbitIdeal_of_aeval_eq_zero x (isWeightedHomogeneous_homogenize c F) hH)
    exact (aeval_dehomCoords (genPt V) c hyc F).trans
      (mul_eq_zero_of_left ((aeval_genPt_eq_zero_iff V _).mpr hHV) _)
  have hmem : ∀ F, chartEval x c F ∈ chartPoint x c V ↔
      aeval (dehomCoords (genPt V) c) F = 0 := by
    intro F
    constructor
    · intro hF
      obtain ⟨g, hg, hgF⟩ :=
        (Ideal.mem_map_iff_of_surjective _ (chartEval_surjective x c)).mp hF
      have h1 := hker (F - g) (by rw [map_sub, hgF, sub_self])
      rwa [map_sub, hVzero g hg, sub_zero] at h1
    · intro hF
      have hF' := (aeval_dehomCoords (genPt V) c hyc F).symm.trans hF
      have hH := (aeval_genPt_eq_zero_iff V _).mp
        ((mul_eq_zero.mp hF').resolve_right (prod_inv_pow_ne_zero _ c hyc _))
      have e : chartEval x c (homogenize c F) = chartEval x c F :=
        map_homogenize c (chartEval x c).toRingHom (chartEval_X_chart x c hxc) F
      rw [← e]
      exact Ideal.mem_map_of_mem _ hH

  have hformV : ∀ G D, IsWeightedHomogeneous (coordDeg n) G D →
      (chartEval x c G ∈ chartPoint x c V ↔ G ∈ V) := fun G D hG ↦ by
    rw [hmem, aeval_dehomCoords_of_homog (genPt V) c hG, mul_eq_zero,
      or_iff_left (prod_inv_pow_ne_zero _ c hyc _), aeval_genPt_eq_zero_iff]

  have hhom : ∀ F, chartEval x c (homogenize c F) = chartEval x c F := fun F ↦
    map_homogenize c (chartEval x c).toRingHom (chartEval_X_chart x c hxc) F

  set M : ι → ℝ := fun k ↦ ⨆ i, v (coordVec x k i) with hMdef
  have hMle : ∀ k i, v (coordVec x k i) ≤ M k := fun k i ↦
    le_ciSup (Set.finite_range fun i ↦ v (coordVec x k i)).bddAbove i
  have hy0 : ∀ k, coordVec x k (c k) ≠ 0 := fun k h ↦ hxc k (congrArg Subtype.val h)
  have hvpos : ∀ k, 0 < v (coordVec x k (c k)) := fun k ↦ FinitePlace.pos_iff.mpr (hy0 k)
  let φ : MvPolynomial (Coord n) ℤ →ₐ[ℤ] coordField x :=
    aeval (dehomCoords (fun p : Coord n ↦ coordVec x p.1 p.2) c)
  have hincl : ∀ F, IntermediateField.inclusion (ratioField_le_coordField x)
      (chartEval x c F : ratioField x) = φ F := by
    intro F
    have h : (IntermediateField.inclusion (ratioField_le_coordField x)).toRingHom.comp
        ((chartRing x c).val.toRingHom.comp (chartEval x c).toRingHom) =
        (φ : MvPolynomial (Coord n) ℤ →+* coordField x) :=
      MvPolynomial.ringHom_ext (fun m ↦ by simp) (fun p ↦ by
        apply Subtype.ext
        simp [φ, chartEval, chartRatio, dehomCoords, coordVec, div_eq_inv_mul])
    exact DFunLike.congr_fun h F
  have hφG : ∀ G D, IsWeightedHomogeneous (coordDeg n) G D →
      φ G = evalCone (coordVec x) G * ∏ k, (coordVec x k (c k))⁻¹ ^ D k := fun G D hG ↦ by
    refine (aeval_dehomCoords_of_homog _ c hG).trans ?_
    rw [aeval_def, evalCone, Subsingleton.elim (algebraMap ℤ (coordField x)) (Int.castRingHom _)]

  have hle : (∀ k, v (coordVec x k (c k)) = M k) → ∀ F, v (φ F) ≤ 1 := fun hcM ↦
    finitePlace_aeval_le_one v _ fun p ↦ by
      simp only [dehomCoords, map_mul, map_inv₀]
      rw [inv_mul_le_one₀ (hvpos p.1), hcM]
      exact hMle p.1 p.2
  have hlt : (∀ k, v (coordVec x k (c k)) = M k) → ∀ G D,
      IsWeightedHomogeneous (coordDeg n) G D → (v (φ G) < 1 ↔ G ∈ orbitCenter x v) :=
    fun hcM G D hG ↦ by
      have hP : 0 < ∏ k, M k ^ D k :=
        Finset.prod_pos fun k _ ↦ pow_pos (hcM k ▸ hvpos k) _
      rw [OrbitCenterMemIff.proof ι n x hx v G D ((geoMultiHomog_iff G D).mpr hG), hφG G D hG,
        map_mul, map_prod]
      simp_rw [map_pow, map_inv₀, hcM, inv_pow]
      rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, div_lt_one hP]
  simp only [AbsCentredAt]
  constructor
  · intro h
    have hcM : ∀ k, v (coordVec x k (c k)) = M k := fun k ↦
      le_antisymm (hMle k (c k)) (not_lt.mp fun hlt' ↦ hc k (h ▸ X_mem_orbitCenter x v k (c k) hlt'))
    refine ⟨fun u ↦ ?_, fun u ↦ ?_⟩
    · obtain ⟨F, rfl⟩ := chartEval_surjective x c u
      rw [hincl]
      exact hle hcM F
    · obtain ⟨F, rfl⟩ := chartEval_surjective x c u
      rw [← hhom F, hincl, hlt hcM _ _ (isWeightedHomogeneous_homogenize c F), h,
        hformV _ _ (isWeightedHomogeneous_homogenize c F)]
  · rintro ⟨h1, h2⟩
    have hcM : ∀ k, v (coordVec x k (c k)) = M k := fun k ↦ by
      refine le_antisymm (hMle k (c k)) (ciSup_le fun i ↦ ?_)
      have := h1 (chartEval x c (X ⟨k, i⟩))
      rw [hincl] at this
      simpa [φ, dehomCoords, inv_mul_le_one₀ (hvpos k)] using this
    have hiff : ∀ G D, IsWeightedHomogeneous (coordDeg n) G D → (G ∈ orbitCenter x v ↔ G ∈ V) :=
      fun G D hG ↦ by
        rw [← hlt hcM G D hG, ← hformV G D hG, ← h2, hincl]
    refine le_antisymm (Ideal.span_le.mpr fun F ⟨d, hFd, hFlt⟩ ↦ ?_) fun f hf ↦ ?_
    · exact (hiff F d ((geoMultiHomog_iff F d).mp hFd)).mp (Ideal.subset_span ⟨d, hFd, hFlt⟩)
    · rw [← sum_weightedHomogeneousComponent (w := coordDeg n) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ ↦ (hiff _ b
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).mpr (hVh f hf b)

end GroundTheory.Heights₂.Heights

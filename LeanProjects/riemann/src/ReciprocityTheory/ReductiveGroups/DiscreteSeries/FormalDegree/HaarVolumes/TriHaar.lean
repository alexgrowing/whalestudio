import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriHaarA

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.UpperTriangularMatrices

variable {N : ℕ}

theorem upMat_triCoOf_mul (t t0 : TriCo N) :
    upMat (triCoOf (upMat t * upMat t0)) = upMat t * upMat t0 ∧
      ∀ j, (triCoOf (upMat t * upMat t0)).1 j = t.1 j * t0.1 j := by
  have hU : ∀ (s : TriCo N) (a b : Fin N), upMat s a b =
      if a = b then ((s.1 a : ℝ) : ℂ) else if h : a < b then s.2 ⟨(a, b), h⟩ else 0 :=
    fun s a b => rfl
  have hz : ∀ (s : TriCo N) (a b : Fin N), b < a → upMat s a b = 0 := by
    intro s a b h
    rw [hU s a b, if_neg (ne_of_gt h), dif_neg (not_lt.mpr h.le)]
  have hlow : ∀ a b : Fin N, b < a → (upMat t * upMat t0) a b = 0 := by
    intro a b hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases hka : k < a
    · rw [hz t a k hka, zero_mul]
    · rw [hz t0 k b (lt_of_lt_of_le hba (not_lt.mp hka)), mul_zero]
  have hdiag : ∀ a, (upMat t * upMat t0) a a = ((t.1 a * t0.1 a : ℝ) : ℂ) := by
    intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hU t a a, hU t0 a a, if_pos rfl, if_pos rfl, Complex.ofReal_mul]
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · rw [hz t a k h, zero_mul]
      · rw [hz t0 k a h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h
  refine ⟨?_, fun j => ?_⟩
  · ext a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hU _ a b, if_neg (ne_of_lt h), dif_pos h]
      rfl
    · subst h
      rw [hU _ a a, if_pos rfl]
      show (((upMat t * upMat t0) a a).re : ℂ) = (upMat t * upMat t0) a a
      rw [hdiag, Complex.ofReal_re]
    · rw [hU _ a b, if_neg (ne_of_gt h), dif_neg (not_lt.mpr h.le), hlow a b h]
  · show ((upMat t * upMat t0) j j).re = t.1 j * t0.1 j
    rw [hdiag, Complex.ofReal_re]

theorem triMeas_map_mul_right (t0 : TriCo N) (h0 : t0 ∈ triPos N) :
    Measure.map (fun t : TriCo N => triCoOf (upMat t * upMat t0)) (triMeas N) = triMeas N := by
  classical
  have hfun : (fun t : TriCo N => triCoOf (upMat t * upMat t0)) = ⇑(rmulL (upMat t0)) := by
    funext t
    rw [rmulL_apply]
  set L : TriCo N →ₗ[ℝ] TriCo N := rmulL (upMat t0) with hL
  have hdet : LinearMap.det L = ∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1) := det_rmulL_upMat t0 h0
  set D : ℝ := ∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1) with hD
  have hDpos : 0 < D := Finset.prod_pos fun j _ => pow_pos (h0 j) _
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  haveI hC : (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)).IsAddHaarMeasure := by
    first
      | infer_instance
      | exact Measure.pi.isAddHaarMeasure _
  haveI hR : (volume : Measure (Fin N → ℝ)).IsAddHaarMeasure := by
    first
      | infer_instance
      | exact Measure.pi.isAddHaarMeasure _
  haveI hT : (volume : Measure (TriCo N)).IsAddHaarMeasure := by
    first
      | exact Measure.prod.instIsAddHaarMeasure volume volume
      | infer_instance
  have hvol : Measure.map L (volume : Measure (TriCo N)) = ENNReal.ofReal |D⁻¹| • volume := by
    rw [← hdet]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact hDpos.ne')
  have hP : MeasurableSet (triPos N) := by
    have : triPos N = ⋂ j : Fin N, {t : TriCo N | 0 < t.1 j} := by
      ext t
      simp [triPos]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)
  have hpre : ∀ S : Set (TriCo N), L ⁻¹' S ∩ triPos N = L ⁻¹' (S ∩ triPos N) := by
    intro S
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [hL, rmulL_mem_triPos t0 x h0]
  rw [hfun]
  ext s hs
  have hS : MeasurableSet (s ∩ triPos N) := hs.inter hP
  rw [Measure.map_apply hLm hs, triMeas, withDensity_apply _ (hLm hs), withDensity_apply _ hs,
    Measure.restrict_restrict (hLm hs), Measure.restrict_restrict hs, hpre s]
  have h1 : ∫⁻ x in L ⁻¹' (s ∩ triPos N), triDens x =
      ∫⁻ x in L ⁻¹' (s ∩ triPos N), ENNReal.ofReal D * triDens (L x) := by
    refine lintegral_congr fun x => ?_
    rw [hL, hD, ← triDens_rmulL t0 x h0]
  have h2 : ∫⁻ x in L ⁻¹' (s ∩ triPos N), ENNReal.ofReal D * triDens (L x) =
      ENNReal.ofReal D * ∫⁻ x, (s ∩ triPos N).indicator triDens (L x) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator (hLm hS)]
    congr 1
  have h3 : ∫⁻ x, (s ∩ triPos N).indicator triDens (L x) =
      ENNReal.ofReal |D⁻¹| * ∫⁻ y in s ∩ triPos N, triDens y := by
    rw [← lintegral_map ((triDens_measurable).indicator hS) hLm, hvol, lintegral_smul_measure,
      lintegral_indicator hS]
    rfl
  rw [h1, h2, h3, ← mul_assoc, ← ENNReal.ofReal_mul hDpos.le, abs_of_pos (inv_pos.mpr hDpos),
    mul_inv_cancel₀ hDpos.ne', ENNReal.ofReal_one, one_mul]

theorem triMeas_compact_lt_top (K : Set (TriCo N)) (hK : IsCompact K) (hK0 : K ⊆ triPos N) :
    triMeas N K < ⊤ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  unfold triMeas
  rw [withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_eq_left.mpr hK0]
  have hgc : ContinuousOn (fun t : TriCo N => ∏ j : Fin N, t.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1))) K := by
    refine continuousOn_finset_prod _ (fun j _ => ?_)
    exact ContinuousOn.zpow₀ (by fun_prop : Continuous fun t : TriCo N => t.1 j).continuousOn _
      (fun x hx => Or.inl (hK0 hx j).ne')
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hgc
  calc ∫⁻ a in K, triDens a ≤ ∫⁻ _ in K, ENNReal.ofReal C := by
        refine setLIntegral_mono' hKm (fun x hx => ?_)
        exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC x hx))
    _ = ENNReal.ofReal C * volume K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end ReciprocityTheory.ChartRestriction.DS

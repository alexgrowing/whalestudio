import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsLinearIndependentSqrtEqSuccMinQuad
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LinearIndependentRealOfIntOfDiscrete
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DiscreteTopologySpanOfLinearIndependent

noncomputable section

open Module Submodule MeasureTheory

namespace GlobalTheory

section FirstTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem measure_le_two_pow_mul_covolume (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} (hsymm : ∀ x ∈ s, -x ∈ s) (hconv : Convex ℝ s)
    (hL : ∀ x ∈ L, x ≠ 0 → x ∉ s) :
    μ s ≤ ENNReal.ofReal (2 ^ finrank ℝ E * ZLattice.covolume L μ) := by
  by_contra! hlt
  let b := Free.chooseBasis ℤ L
  have fund : IsAddFundamentalDomain L.toAddSubgroup
      (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) μ :=
    ZLattice.isAddFundamentalDomain b μ
  have hc : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain L μ
    (ZLattice.isAddFundamentalDomain b μ)
  have hfin : μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund
    hsymm hconv (by
      rwa [← ENNReal.ofReal_toReal hfin, ← measureReal_def, ← hcov, ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_pow (by norm_num),
        ← ENNReal.ofReal_mul (ZLattice.covolume_pos L μ).le, mul_comm])
  exact hL x x.2 (fun h ↦ hx0 (Subtype.ext h)) hxs

end FirstTheorem

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_linearMap_det_eq_prod_inv_succMin (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∃ T : E →ₗ[ℝ] E, LinearMap.det T = (∏ i : Fin (finrank ℝ E), succMin L (i + 1))⁻¹ ∧
      ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖T x‖ := by
  obtain ⟨b, hbL, hbN⟩ := exists_basis_norm_eq_succMin L
  have h : finrank ℝ E = Fintype.card (Fin (finrank ℝ E)) := (Fintype.card_fin _).symm
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis h b
  let l : Fin (finrank ℝ E) → ℝ := fun i ↦ succMin L (i + 1)
  have hl : ∀ i, 0 < l i := fun i ↦ succMin_pos_of_isZLattice (by omega) i.2
  let T : E →ₗ[ℝ] E := Matrix.toLin o.toBasis o.toBasis (Matrix.diagonal fun i ↦ (l i)⁻¹)
  have hT : ∀ x i, o.repr (T x) i = (l i)⁻¹ * o.repr x i := by
    intro x i
    have := Matrix.repr_toLin o.toBasis o.toBasis (Matrix.diagonal fun i ↦ (l i)⁻¹) x
    have h2 := congrFun this i
    rw [Matrix.mulVec_diagonal] at h2
    exact h2
  refine ⟨T, ?_, fun x hx h0 ↦ ?_⟩
  · rw [LinearMap.det_toLin, Matrix.det_diagonal, Finset.prod_inv_distrib]
  · have hne : (Finset.univ.filter fun i ↦ o.repr x i ≠ 0).Nonempty := by
      by_contra hc
      apply h0
      apply o.repr.injective
      ext i
      simpa using (Finset.filter_eq_empty_iff.1 (Finset.not_nonempty_iff_eq_empty.1 hc)
        (Finset.mem_univ i))
    obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image _ id hne
    have hk0 : o.repr x k ≠ 0 := (Finset.mem_filter.1 hk).2
    have hspan : x ∉ span ℝ (b '' {j | (j : ℕ) < k}) := by
      intro hmem
      have hle : span ℝ (b '' {j | (j : ℕ) < k}) ≤ LinearMap.ker (o.toBasis.coord k) := by
        refine span_le.2 ?_
        rintro _ ⟨j, hj, rfl⟩
        exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular' h b
          (show j < k from hj)
      exact hk0 (hle hmem)
    have hx1 : l k ≤ ‖x‖ :=
      succMin_le_norm_of_notMem_span b.linearIndependent hbL (fun j ↦ (hbN j).le) k.2.le hx hspan
    have hcmp : ‖(l k)⁻¹ • x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
      rw [← o.repr.norm_map, ← o.repr.norm_map, EuclideanSpace.norm_sq_eq,
        EuclideanSpace.norm_sq_eq]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [hT, map_smul, PiLp.smul_apply, smul_eq_mul]
      by_cases hi : o.repr x i = 0
      · simp [hi]
      · have hik : i ≤ k := hmax i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        have hlik : l i ≤ l k :=
          succMin_mono_of_isZLattice (Nat.succ_le_succ hik) k.2
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (inv_pos.2 (hl i)).le,
          Real.norm_of_nonneg (inv_pos.2 (hl k)).le]
        have := hl i
        have := hl k
        gcongr
    refine le_trans ?_ (le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hcmp)
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 (hl k)).le, le_inv_mul_iff₀ (hl k), mul_one]
    exact hx1

variable [MeasurableSpace E] [BorelSpace E]

theorem volume_real_unitBall_pos : 0 < volume.real (Metric.ball (0 : E) 1) :=
  ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne

variable (E) in

theorem two_div_sqrt_pow_le_volume_unitBall :
    (2 / √(finrank ℝ E : ℝ)) ^ finrank ℝ E ≤ volume.real (Metric.ball (0 : E) 1) := by
  let o := stdOrthonormalBasis ℝ E
  let f : E →ₗ[ℝ] (Fin (finrank ℝ E) → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin (finrank ℝ E) → ℝ)).toLinearMap ∘ₗ o.repr.toLinearEquiv.toLinearMap
  have hf : MeasurePreserving f := (PiLp.volume_preserving_ofLp _).comp o.measurePreserving_repr
  set r : ℝ := (√(finrank ℝ E : ℝ))⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hs : volume (f ⁻¹' Metric.closedBall 0 r) = ENNReal.ofReal ((2 * r) ^ finrank ℝ E) := by
    rw [hf.measure_preimage Metric.isClosed_closedBall.measurableSet.nullMeasurableSet,
      Real.volume_pi_closedBall _ hr0, Fintype.card_fin]
  have hsub : f ⁻¹' Metric.closedBall 0 r ⊆ Metric.closedBall (0 : E) 1 := by
    intro x hx
    have hi : ∀ i, ‖o.repr x i‖ ≤ r := fun i ↦
      (pi_norm_le_iff_of_nonneg hr0).1 (mem_closedBall_zero_iff.1 hx) i
    rw [mem_closedBall_zero_iff, ← sq_le_one_iff₀ (norm_nonneg _), ← o.repr.norm_map,
      EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖o.repr x i‖ ^ 2 ≤ ∑ _i : Fin (finrank ℝ E), r ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ by have := hi i; gcongr
      _ = finrank ℝ E * (finrank ℝ E : ℝ)⁻¹ := by simp [hr]
      _ ≤ 1 := mul_inv_le_one
  have h := measure_mono (μ := volume) hsub
  rw [hs, Measure.addHaar_unitClosedBall_eq_addHaar_unitBall,
    ENNReal.ofReal_le_iff_le_toReal measure_ball_lt_top.ne] at h
  rwa [div_eq_mul_inv]

variable (E) in

theorem two_pow_div_volume_unitBall_le :
    2 ^ finrank ℝ E / volume.real (Metric.ball (0 : E) 1) ≤
      (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) := by
  have h := two_div_sqrt_pow_le_volume_unitBall E
  have h2 : (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) = √(finrank ℝ E : ℝ) ^ finrank ℝ E := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 1; ring
  have h3 : 0 < √(finrank ℝ E : ℝ) ^ finrank ℝ E := by
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hpos
    · simp [h0]
    · positivity
  rw [div_pow, div_le_iff₀ h3] at h
  rwa [h2, div_le_iff₀ volume_real_unitBall_pos, mul_comm]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem prod_succMin_mul_volume_unitBall_le :
    (∏ i : Fin (finrank ℝ E), succMin L (i + 1)) * volume.real (Metric.ball (0 : E) 1) ≤
      2 ^ finrank ℝ E * ZLattice.covolume L := by
  obtain ⟨T, hdet, hT⟩ := exists_linearMap_det_eq_prod_inv_succMin L
  have hP : 0 < ∏ i : Fin (finrank ℝ E), succMin L (i + 1) :=
    Finset.prod_pos fun i _ ↦ succMin_pos_of_isZLattice (by omega) i.2
  have h := measure_le_two_pow_mul_covolume L volume (s := T ⁻¹' Metric.ball 0 1)
    (fun x hx ↦ by simpa using hx) ((convex_ball 0 1).linear_preimage T)
    (fun x hx h0 hs ↦ (hT x hx h0).not_gt (mem_ball_zero_iff.1 hs))
  have hc := ZLattice.covolume_pos L volume
  rw [Measure.addHaar_preimage_linearMap _ (by rw [hdet]; positivity), hdet, inv_inv,
    abs_of_pos hP, ← ofReal_measureReal measure_ball_lt_top.ne, ← ENNReal.ofReal_mul hP.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h

theorem prod_succMin_le_two_pow_div_mul_covolume :
    ∏ i : Fin (finrank ℝ E), succMin L (i + 1) ≤
      2 ^ finrank ℝ E / volume.real (Metric.ball (0 : E) 1) * ZLattice.covolume L := by
  rw [div_mul_eq_mul_div, le_div_iff₀ volume_real_unitBall_pos]
  exact prod_succMin_mul_volume_unitBall_le L

theorem prod_succMin_le_rpow_mul_covolume :
    ∏ i : Fin (finrank ℝ E), succMin L (i + 1) ≤
      (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) * ZLattice.covolume L :=
  (prod_succMin_le_two_pow_div_mul_covolume L).trans
    (mul_le_mul_of_nonneg_right (two_pow_div_volume_unitBall_le E)
      (ZLattice.covolume_pos L volume).le)

theorem succMin_mul_minNorm_pow_le {k : ℕ} (h1 : 1 ≤ k) (hk : k ≤ finrank ℝ E) :
    succMin L k * minNorm L ^ (finrank ℝ E - 1) ≤
      (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) * ZLattice.covolume L := by
  refine le_trans ?_ (prod_succMin_le_rpow_mul_covolume L)
  let j : Fin (finrank ℝ E) := ⟨k - 1, by omega⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), show (j : ℕ) + 1 = k by simp [j]; omega]
  refine mul_le_mul_of_nonneg_left ?_ (succMin_nonneg L k)
  calc minNorm L ^ (finrank ℝ E - 1) = ∏ _i ∈ Finset.univ.erase j, minNorm L := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ succMin_nonneg L 1) fun i _ ↦
        succMin_mono_of_isZLattice (by omega) i.2

end Euclidean

section Discrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]

theorem prod_succMin_le_rpow_mul_spanCovol :
    ∏ i : Fin (finrank ℤ L), succMin L (i + 1) ≤
      (finrank ℤ L : ℝ) ^ ((finrank ℤ L : ℝ) / 2) * spanCovol L := by
  borelize E
  have h := prod_succMin_le_rpow_mul_covolume (inSpan L)
  simp only [succMin_inSpan] at h
  rw [spanCovol_eq_covolume_comap_span, ← finrank_span_eq_finrank_int]
  exact h

end Discrete

end GlobalTheory

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def metricDefect (A : HermLine n) (z : Cone n ℂ) : ℝ :=
  Real.log (A.metric z) - ∑ k, (A.deg k : ℝ) * Real.log (l2Norm (z k))

omit [DecidableEq ι] in

theorem metricDefect_smul (A : HermLine n) (c : ι → ℂ) (z : Cone n ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : BlockNonzero z) :
    metricDefect A (fun k i ↦ c k * z k i) = metricDefect A z := by
  have hcn : ∀ k, 0 < ‖c k‖ := fun k ↦ norm_pos_iff.mpr (hc k)
  have hl : ∀ k, 0 < l2Norm (z k) := fun k ↦ vectorL2Norm_pos (hz k)
  unfold metricDefect
  rw [A.metric_smul c z hc hz, Real.log_mul (Finset.prod_pos fun k _ ↦ zpow_pos (hcn k) _).ne'
    (A.metric_pos z hz).ne', Real.log_prod (fun k _ ↦ (zpow_pos (hcn k) _).ne')]
  have e : ∀ k, l2Norm (fun i ↦ c k * z k i) = ‖c k‖ * l2Norm (z k) := fun k ↦ vectorL2Norm_const_mul _ _
  simp only [e, Real.log_zpow]
  simp only [show ∀ k, Real.log (‖c k‖ * l2Norm (z k)) = Real.log ‖c k‖ + Real.log (l2Norm (z k)) from
    fun k ↦ Real.log_mul (hcn k).ne' (hl k).ne']
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem continuous_l2Norm {m : ℕ} : Continuous (fun w : Fin m → ℂ ↦ l2Norm w) :=
  Real.continuous_sqrt.comp
    (continuous_finsetSum _ fun i _ ↦ (continuous_norm.comp (continuous_apply i)).pow 2)

variable (n) in

def unitSpheres : Set (Cone n ℂ) := {z | ∀ k, l2Norm (z k) = 1}

omit [DecidableEq ι] in
theorem isCompact_unitSpheres : IsCompact (unitSpheres n) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have : unitSpheres n = ⋂ k, {z : Cone n ℂ | l2Norm (z k) = 1} := by
      ext z; simp [unitSpheres]
    rw [this]
    exact isClosed_iInter fun k ↦
      isClosed_eq (continuous_l2Norm.comp (continuous_apply k)) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Cone n ℂ)) (r := 1)).subset fun z hz ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k ↦
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i ↦ ?_
    rw [← hz k]
    exact norm_le_l2Norm (z k) i

omit [DecidableEq ι] in

theorem exists_bound_metricDefect (A : HermLine n) :
    ∃ M, ∀ z : Cone n ℂ, BlockNonzero z → |metricDefect A z| ≤ M := by
  have hsub : unitSpheres n ⊆ {z | BlockNonzero z} := fun z hz k h ↦ by
    have := hz k
    rw [h] at this
    simp [l2Norm] at this
  have hcont : ContinuousOn (metricDefect A) {z | BlockNonzero z} := by
    unfold metricDefect
    refine ContinuousOn.sub (A.metric_smooth.continuousOn.log fun z hz ↦ (A.metric_pos z hz).ne') ?_
    refine continuousOn_finsetSum _ fun k _ ↦ continuousOn_const.mul ?_
    exact ((continuous_l2Norm.comp (continuous_apply k)).continuousOn).log
      fun z hz ↦ (vectorL2Norm_pos (hz k)).ne'
  obtain ⟨M, hM⟩ := isCompact_unitSpheres.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨M, fun z hz ↦ ?_⟩
  let c : ι → ℂ := fun k ↦ (((l2Norm (z k))⁻¹ : ℝ) : ℂ)
  have hc : ∀ k, c k ≠ 0 := fun k ↦ by
    simp only [c, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (vectorL2Norm_pos (hz k)).ne'
  have hw : (fun k i ↦ c k * z k i) ∈ unitSpheres n := by
    intro k
    change l2Norm (fun i ↦ c k * z k i) = 1
    rw [vectorL2Norm_const_mul, Complex.norm_of_nonneg (inv_nonneg.mpr (vectorL2Norm_pos (hz k)).le)]
    exact inv_mul_cancel₀ (vectorL2Norm_pos (hz k)).ne'
  have := hM _ hw
  rwa [metricDefect_smul A c z hc hz, Real.norm_eq_abs] at this

omit [Fintype ι] [DecidableEq ι] in

theorem metricDefect_standard [Fintype ι] (z : Cone n ℂ) (hz : BlockNonzero z) :
    metricDefect (HermLine.standard n) z = 0 := by
  unfold metricDefect
  change Real.log (∏ k, l2Norm (z k)) - ∑ k, ((1 : ℤ) : ℝ) * Real.log (l2Norm (z k)) = 0
  rw [Real.log_prod (fun k _ ↦ (vectorL2Norm_pos (hz k)).ne')]
  simp

section Blocks

variable {K : Type*} [Field K] [NumberField K]

def blockFin (y : Cone n K) (k : ι) (v : FinitePlace K) : ℝ := Real.log (⨆ i, v (y k i))

def blockSum (y : Cone n K) (k : ι) : ℝ :=
  (∑ᶠ v : FinitePlace K, blockFin y k v) + ∑ σ : K →+* ℂ, Real.log (l2Norm fun i ↦ σ (y k i))

omit [Fintype ι] [DecidableEq ι] in

theorem finite_support_blockFin (y : Cone n K) (k : ι) (hy : y k ≠ 0) :
    (Function.support (blockFin y k)).Finite := by
  classical
  have hT : (⋃ i ∈ {i | y k i ≠ 0}, Function.mulSupport fun w : FinitePlace K ↦ w (y k i)).Finite :=
    Set.Finite.biUnion (Set.toFinite _) fun i hi ↦ FinitePlace.hasFiniteMulSupport hi
  refine hT.subset fun v hv ↦ ?_
  by_contra hvT
  apply hv
  have h1 : ∀ i, y k i ≠ 0 → v (y k i) = 1 := by
    intro i hi
    by_contra hne
    exact hvT (Set.mem_biUnion (x := i) hi hne)
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  have hs : (⨆ i, v (y k i)) = 1 := by
    refine le_antisymm (ciSup_le fun i ↦ ?_) (le_ciSup_of_le (Set.finite_range _).bddAbove i0 ?_)
    · by_cases h : y k i = 0
      · rw [h, map_zero]; exact zero_le_one
      · exact (h1 i h).le
    · exact (h1 i0 hi0).ge
  simp only [blockFin, hs, Real.log_one]

theorem sum_log_places_eq_zero {t : K} (ht : t ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log (v t)) + ∑ σ : K →+* ℂ, Real.log ‖σ t‖ = 0 := by
  have hfin : (Function.mulSupport fun w : FinitePlace K ↦ w t).Finite :=
    FinitePlace.hasFiniteMulSupport ht
  have hprod := FinitePlace.prod_eq_inv_abs_norm ht
  rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _
    (fun v hv ↦ Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hv))] at hprod
  have hsupp : (Function.support fun v : FinitePlace K ↦ Real.log (v t)) ⊆ hfin.toFinset := by
    intro v hv
    refine Finset.mem_coe.mpr (hfin.mem_toFinset.mpr fun h ↦ hv ?_)
    simp only [h, Real.log_one]
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    ← Real.log_prod (fun v _ ↦ (FinitePlace.pos_iff.mpr ht).ne'), hprod]
  have h1 : (((Algebra.norm ℚ t : ℚ) : ℂ)) = ∏ σ : K →+* ℂ, σ t := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ t
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun σ ↦ rfl).symm
  rw [← Real.log_prod (fun σ _ ↦ by rw [norm_ne_zero_iff, map_ne_zero]; exact ht),
    ← norm_prod, ← h1, Complex.norm_ratCast]
  push_cast
  rw [Real.log_inv]
  ring

omit [Fintype ι] [DecidableEq ι] in

theorem blockSum_nonneg (y : Cone n K) (k : ι) (hy : y k ≠ 0) : 0 ≤ blockSum y k := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  have ht : y k i0 ≠ 0 := hi0
  have hfin := finite_support_blockFin y k hy
  have hfin2 : (Function.support fun v : FinitePlace K ↦ Real.log (v (y k i0))).Finite := by
    refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport ht) fun v hv h ↦ hv ?_
    simp only [h, Real.log_one]
  classical
  let T := hfin.toFinset ∪ hfin2.toFinset
  have e1 : ∑ᶠ v, blockFin y k v = ∑ v ∈ T, blockFin y k v :=
    finsum_eq_sum_of_support_subset _ fun v hv ↦ by
      simp only [T, Finset.coe_union, Set.mem_union, Finset.mem_coe, hfin.mem_toFinset]
      exact Or.inl hv
  have e2 : ∑ᶠ v : FinitePlace K, Real.log (v (y k i0)) = ∑ v ∈ T, Real.log (v (y k i0)) :=
    finsum_eq_sum_of_support_subset _ fun v hv ↦ by
      simp only [T, Finset.coe_union, Set.mem_union, Finset.mem_coe, hfin2.mem_toFinset]
      exact Or.inr hv
  have hle1 : ∑ v ∈ T, Real.log (v (y k i0)) ≤ ∑ v ∈ T, blockFin y k v :=
    Finset.sum_le_sum fun v _ ↦ Real.log_le_log (FinitePlace.pos_iff.mpr ht)
      (le_ciSup (f := fun i ↦ v (y k i)) (Set.finite_range _).bddAbove i0)
  have hle2 : ∑ σ : K →+* ℂ, Real.log ‖σ (y k i0)‖ ≤
      ∑ σ : K →+* ℂ, Real.log (l2Norm fun i ↦ σ (y k i)) :=
    Finset.sum_le_sum fun σ _ ↦ Real.log_le_log (norm_pos_iff.mpr ((map_ne_zero σ).mpr ht))
      (norm_le_l2Norm (fun i ↦ σ (y k i)) i0)
  have h0 := sum_log_places_eq_zero ht
  unfold blockSum
  rw [e1]
  rw [e2] at h0
  linarith

end Blocks

omit [Fintype ι] [DecidableEq ι] in
theorem coordVec_ne_zero {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) (k : ι) :
    coordVec x k ≠ 0 := by
  intro h
  apply hx k
  funext i
  exact congrArg Subtype.val (congrFun h i)

omit [Fintype ι] [DecidableEq ι] in
theorem blockNonzero_sigma {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x)
    (σ : coordField x →+* ℂ) : BlockNonzero (fun k i ↦ σ (coordVec x k i)) := by
  intro k h
  apply coordVec_ne_zero hx k
  funext i
  exact (map_eq_zero σ).mp (congrFun h i)

omit [DecidableEq ι] in

theorem height_eq_blockSum (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ))
    (hx : BlockNonzero x) :
    height A x = ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ *
      (∑ k, (A.deg k : ℝ) * blockSum (coordVec x) k +
        ∑ σ : coordField x →+* ℂ, metricDefect A (fun k i ↦ σ (coordVec x k i))) := by
  have hfin : ∀ k, (Function.support (blockFin (coordVec x) k)).Finite :=
    fun k ↦ finite_support_blockFin _ k (coordVec_ne_zero hx k)
  have hF : (∑ᶠ v : FinitePlace (coordField x),
      ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))) =
      ∑ k, (A.deg k : ℝ) * ∑ᶠ v, blockFin (coordVec x) k v := by
    rw [finsum_sum_comm]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [mul_finsum]
      rfl
    · intro k _
      exact (hfin k).subset (Function.support_mul_subset_right _ _)
  have hA : ∀ σ : coordField x →+* ℂ, Real.log (A.metric fun k i ↦ σ (coordVec x k i)) =
      metricDefect A (fun k i ↦ σ (coordVec x k i)) +
        ∑ k, (A.deg k : ℝ) * Real.log (l2Norm fun i ↦ σ (coordVec x k i)) := by
    intro σ
    unfold metricDefect
    ring
  have hB : ∑ σ : coordField x →+* ℂ,
      ∑ k, (A.deg k : ℝ) * Real.log (l2Norm fun i ↦ σ (coordVec x k i)) =
      ∑ k, (A.deg k : ℝ) * ∑ σ : coordField x →+* ℂ, Real.log (l2Norm fun i ↦ σ (coordVec x k i)) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  unfold height
  rw [hF, Finset.sum_congr rfl fun σ _ ↦ hA σ, Finset.sum_add_distrib, hB]
  unfold blockSum
  simp only [mul_add, Finset.sum_add_distrib]
  ring

omit [DecidableEq ι] in

theorem height_standard_eq_blockSum (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x) :
    height (HermLine.standard n) x = ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ *
      ∑ k, blockSum (coordVec x) k := by
  rw [height_eq_blockSum _ x hx]
  have h0 : ∀ σ : coordField x →+* ℂ,
      metricDefect (HermLine.standard n) (fun k i ↦ σ (coordVec x k i)) = 0 :=
    fun σ ↦ metricDefect_standard _ (blockNonzero_sigma hx σ)
  simp only [h0, Finset.sum_const_zero, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  change ((1 : ℤ) : ℝ) * _ = _
  rw [Int.cast_one, one_mul]

theorem heightComparison : HeightComparison.Statement := by
  intro ι _ _ n P A
  obtain ⟨M, hM⟩ := exists_bound_metricDefect A
  refine ⟨∑ k, (A.deg k).natAbs, M, fun x hx ↦ ?_⟩
  have hxb : BlockNonzero x := hx.1
  have hd : (0 : ℝ) < Module.finrank ℚ (coordField x) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := coordField x)
  have hnn : ∀ k, 0 ≤ blockSum (coordVec x) k :=
    fun k ↦ blockSum_nonneg _ k (coordVec_ne_zero hxb k)
  rw [height_eq_blockSum A x hxb, height_standard_eq_blockSum x hxb]
  set d : ℝ := (Module.finrank ℚ (coordField x) : ℝ)
  set N : ℝ := ((∑ k, (A.deg k).natAbs : ℕ) : ℝ)
  have hR : |∑ σ : coordField x →+* ℂ, metricDefect A (fun k i ↦ σ (coordVec x k i))| ≤ d * M := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ M fun σ _ ↦ hM _ (blockNonzero_sigma hxb σ)).trans ?_
    rw [Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  have hak : ∀ k, |(A.deg k : ℝ)| ≤ N := by
    intro k
    have e : |(A.deg k : ℝ)| = ((A.deg k).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e]
    simp only [N, Nat.cast_sum]
    exact Finset.single_le_sum (f := fun j ↦ ((A.deg j).natAbs : ℝ))
      (fun j _ ↦ Nat.cast_nonneg _) (Finset.mem_univ k)
  have hS : |∑ k, (A.deg k : ℝ) * blockSum (coordVec x) k| ≤ N * ∑ k, blockSum (coordVec x) k := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [abs_mul, abs_of_nonneg (hnn k)]
    exact mul_le_mul_of_nonneg_right (hak k) (hnn k)
  rw [abs_mul, abs_of_pos (inv_pos.mpr hd)]
  have hsum := (abs_add_le _ _).trans (add_le_add hS hR)
  calc d⁻¹ * |∑ k, (A.deg k : ℝ) * blockSum (coordVec x) k +
        ∑ σ : coordField x →+* ℂ, metricDefect A (fun k i ↦ σ (coordVec x k i))|
      ≤ d⁻¹ * (N * ∑ k, blockSum (coordVec x) k + d * M) :=
        mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hd).le
    _ = N * (d⁻¹ * ∑ k, blockSum (coordVec x) k) + M := by
        field_simp

end

end GroundTheory.Heights₂.Heights

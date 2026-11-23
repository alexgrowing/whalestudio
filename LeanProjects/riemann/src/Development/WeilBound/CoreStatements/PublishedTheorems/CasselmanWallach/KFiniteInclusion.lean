import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace WeightedEigenSum

theorem pow_eig {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (m : ℝ) (x : V)
    (h : T x = (m : ℂ) • x) (s : ℕ) : ((1 + T) ^ s) x = (((1 + m) ^ s : ℝ) : ℂ) • x := by
  induction s with
  | zero => simp
  | succ k ih =>
    have hx : x + (m : ℂ) • x = (((1 + m : ℝ)) : ℂ) • x := by
      push_cast
      rw [add_smul, one_smul]
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.add_apply, Module.End.one_apply, h, hx,
      smul_smul]
    congr 1
    push_cast
    ring

theorem wsum_le {ι : Type} (μ : ι → ℝ) (hnn : ∀ i, 0 ≤ μ i) (hfin : ∀ R : ℝ, {i | μ i ≤ R}.Finite)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (s : ℕ) (hs : 1 ≤ s) (K : ℝ)
    (hS : ∀ (R : ℝ) (S : Finset ι), (∀ i, i ∈ S ↔ μ i < R) → ∑ i ∈ S, phiR s R (μ i) * a i ≤ K ^ 2)
    (T : Finset ι) : ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i ≤ K ^ 2 := by
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, ∀ i ∈ T, μ i < R0 :=
    ⟨∑ i ∈ T, μ i + 1, fun i hi => by
      have := Finset.single_le_sum (fun j _ => hnn j) hi
      linarith⟩
  have key : ∀ R : ℝ, R0 ≤ R →
      ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i ≤ K ^ 2 := by
    intro R hR
    have hSmem : ∀ i, i ∈ (hfin R).toFinset.filter (fun i => μ i < R) ↔ μ i < R := by
      intro i
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
    have hTS : T ⊆ (hfin R).toFinset.filter (fun i => μ i < R) :=
      fun i hi => (hSmem i).mpr (lt_of_lt_of_le (hR0 i hi) hR)
    have h1 := hS R _ hSmem
    have h2 : ∑ i ∈ T, phiR s R (μ i) * a i ≤
        ∑ i ∈ (hfin R).toFinset.filter (fun i => μ i < R), phiR s R (μ i) * a i :=
      Finset.sum_le_sum_of_subset_of_nonneg hTS (fun i _ _ => mul_nonneg (le_max_right _ _) (ha i))
    have h3 : ∑ i ∈ T, phiR s R (μ i) * a i =
        ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hlt : ((1 + R) ^ s)⁻¹ ≤ ((1 + μ i) ^ s)⁻¹ := by
        apply inv_anti₀ (pow_pos (by linarith [hnn i]) s)
        exact pow_le_pow_left₀ (by linarith [hnn i]) (by linarith [hR0 i hi]) s
      rw [phiR, max_eq_left (by linarith)]
      ring
    linarith
  have hpow : Filter.Tendsto (fun R : ℝ => (1 + R) ^ s) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by omega : s ≠ 0)).comp
      (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
  have ht : Filter.Tendsto
      (fun R : ℝ => ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i) Filter.atTop
      (nhds (∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - 0 * ∑ i ∈ T, a i)) :=
    tendsto_const_nhds.sub ((tendsto_inv_atTop_zero.comp hpow).mul_const _)
  have hlim := le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨R0, key⟩)
  simpa using hlim

end WeightedEigenSum

theorem eigen_weighted_sum_bound : A0 → FunctionalCalculusLaws → B5 := by
  intro _ _ n ε V _ _ E _ ι b μ hb f s K hK hS hs v
  have hv : v = ∑ i ∈ (b.repr v).support, b.repr v i • b i := by
    conv_lhs => rw [← b.linearCombination_repr v]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hpos : ∀ i, 0 < (1 + μ i) ^ s := fun i => pow_pos (by linarith [hb.nonneg i]) s
  have heig : ∀ i, ((1 + casimirK ε E) ^ s) (b i) = (((1 + μ i) ^ s : ℝ) : ℂ) • b i :=
    fun i => WeightedEigenSum.pow_eig _ (μ i) (b i) (hb.eig i) s
  have hw : ((1 + casimirK ε E) ^ s) v =
      ∑ i ∈ (b.repr v).support, (b.repr v i * (((1 + μ i) ^ s : ℝ) : ℂ)) • b i := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, heig, smul_smul]
  have hfv : f v = inner ℂ (∑ i ∈ (b.repr v).support,
      (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i) (((1 + casimirK ε E) ^ s) v) := by
    rw [hw, hb.on.inner_sum]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    have h1 : ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ) * (((1 + μ i) ^ s : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hpos i).ne', Complex.ofReal_one]
    linear_combination (-(b.repr v i * f (b i))) * h1
  have hu2 : ‖∑ i ∈ (b.repr v).support,
      (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i‖ ^ 2 ≤ K ^ 2 := by
    have e : ‖∑ i ∈ (b.repr v).support,
        (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i‖ ^ 2 =
        ∑ i ∈ (b.repr v).support, ‖f (b i)‖ ^ 2 * (((1 + μ i) ^ s)⁻¹) ^ 2 := by
      rw [@norm_sq_eq_re_inner ℂ, hb.on.inner_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hr : 0 ≤ ((1 + μ i) ^ s)⁻¹ := (inv_pos.mpr (hpos i)).le
      rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr, Complex.norm_conj, mul_pow]
    have e2 : ∑ i ∈ (b.repr v).support, ‖f (b i)‖ ^ 2 * (((1 + μ i) ^ s)⁻¹) ^ 2 ≤
        ∑ i ∈ (b.repr v).support, ((1 + μ i) ^ s)⁻¹ * ‖f (b i)‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h0 : 0 ≤ ((1 + μ i) ^ s)⁻¹ := (inv_pos.mpr (hpos i)).le
      have h1 : ((1 + μ i) ^ s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hb.nonneg i]))
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ‖f (b i)‖) h0) (sub_nonneg.mpr h1)]
    have e3 : ∑ i ∈ (b.repr v).support, ((1 + μ i) ^ s)⁻¹ * ‖f (b i)‖ ^ 2 ≤ K ^ 2 :=
      WeightedEigenSum.wsum_le μ hb.nonneg hb.fin (fun i => ‖f (b i)‖ ^ 2) (fun i => sq_nonneg _) s hs K hS _
    linarith
  have hu := (pow_le_pow_iff_left₀ (norm_nonneg _) hK two_ne_zero).mp hu2
  rw [hfv]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg _))

end PositivityTheory.CW

end

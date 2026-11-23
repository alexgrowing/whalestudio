import Mathlib

namespace GlobalTheory

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped nonZeroDivisors NNReal ENNReal

section General

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in

theorem exists_ne_zero_mem_fractionalIdeal_place_le (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (g : InfinitePlace K → ℝ≥0) (h : minkowskiBound K I ≤ volume (convexBodyLT K g)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a ≤ g w := by
  set S : Set (mixedSpace K) :=
    (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => Metric.closedBall 0 (g w))) ×ˢ
    (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } => Metric.closedBall 0 (g w)))
    with hS
  have hsub : convexBodyLT K g ⊆ S :=
    Set.prod_mono (Set.pi_mono fun _ _ => Metric.ball_subset_closedBall)
      (Set.pi_mono fun _ _ => Metric.ball_subset_closedBall)
  have hneg : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    simp only [hS, Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
      mem_closedBall_zero_iff, norm_neg, forall_true_left, Prod.snd_neg] at hx ⊢
    exact hx
  have hconv : Convex ℝ S :=
    Convex.prod (convex_pi (fun _ _ => convex_closedBall _ _))
      (convex_pi (fun _ _ => convex_closedBall _ _))
  have hcomp : IsCompact S :=
    IsCompact.prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
      (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (Submodule.span ℤ
      (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      h_fund hneg hconv hcomp (h.trans (measure_mono hsub))
  rw [Submodule.mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ha, by simpa using h_nz, fun w => ?_⟩
  simp only [hS, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_closedBall_zero_iff] at h_mem
  rw [← normAtPlace_apply]
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw]
    exact h_mem.1 ⟨w, hw⟩
  · rw [normAtPlace_apply_of_isComplex hw]
    exact h_mem.2 ⟨w, hw⟩

end General

section TotallyComplex

variable {E : Type*} [Field E] [NumberField E] [IsTotallyComplex E] {f : ℕ}

theorem exists_ne_zero_mem_fractionalIdeal_norm_sq_le (hf : finrank ℚ E = 2 * f)
    (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0) :
    ∃ a ∈ J, a ≠ 0 ∧ ∀ τ : E →+* ℂ, ‖τ a‖ ^ 2 ≤
      2 / Real.pi * ((FractionalIdeal.absNorm J : ℝ) * √|(discr E : ℝ)|) ^ ((f : ℝ)⁻¹) := by
  classical
  have hc : nrComplexPlaces E = f := by
    have := IsTotallyComplex.finrank E
    omega
  have hr : nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have hf0 : f ≠ 0 := by
    have : 0 < finrank ℚ E := finrank_pos
    omega
  set X : ℝ := (FractionalIdeal.absNorm J : ℝ) * √|(discr E : ℝ)| with hX
  have hN : (0 : ℝ) ≤ (FractionalIdeal.absNorm J : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg J
  have hX0 : 0 ≤ X := mul_nonneg hN (Real.sqrt_nonneg _)
  set B : ℝ := 2 / Real.pi * X ^ ((f : ℝ)⁻¹) with hB
  have hB0 : 0 ≤ B := by positivity
  let R : ℝ≥0 := ⟨√B, Real.sqrt_nonneg _⟩
  have hR : (R : ℝ) ^ 2 = B := Real.sq_sqrt hB0
  obtain ⟨a, ha, ha0, hle⟩ := exists_ne_zero_mem_fractionalIdeal_place_le E
    (Units.mk0 J hJ) (fun _ => R) (by
      rw [convexBodyLT_volume, minkowskiBound,
        volume_fundamentalDomain_fractionalIdealLatticeBasis,
        volume_fundamentalDomain_latticeBasis, mixedEmbedding.finrank,
        Finset.prod_pow_eq_pow_sum, sum_mult_eq, hf, convexBodyLTFactor, hc, hr]
      refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp (le_of_eq ?_)
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.coe_toReal,
        ENNReal.toReal_ofNat, Units.val_mk0, ENNReal.toReal_ofReal hN, pow_zero, one_mul,
        NNReal.coe_pow, NNReal.coe_real_pi, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
      rw [pow_mul (R : ℝ), hR, hB, mul_pow, Real.rpow_inv_natCast_pow hX0 hf0, hX, pow_mul,
        div_pow, show ((2 : ℝ) ^ 2) ^ f = 2 ^ f * 2 ^ f by rw [← mul_pow]; norm_num, inv_pow]
      have := Real.pi_pos
      field_simp)
  refine ⟨a, ha, ha0, fun τ => ?_⟩
  rw [← hR]
  have := hle (InfinitePlace.mk τ)
  rw [InfinitePlace.apply] at this
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

end TotallyComplex

end GlobalTheory

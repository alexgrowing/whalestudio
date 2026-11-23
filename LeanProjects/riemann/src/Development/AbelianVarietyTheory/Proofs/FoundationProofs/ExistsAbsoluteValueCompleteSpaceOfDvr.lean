import Mathlib
open scoped NNReal TensorProduct

namespace GlobalTheory.KLC

open IsDedekindDomain

theorem completeSpace_withAbs_of_unitBall (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K]
    [Algebra R K] [IsFractionRing R K] (f : AbsoluteValue K ℝ)
    (h : ∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) :
    CompleteSpace (WithAbs f) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let em : R →+* WithAbs f := (WithAbs.equiv f).symm.toRingHom.comp (algebraMap R K)
  have hnorm : ∀ x : R, ‖em x‖ = f (algebraMap R K x) := fun x => rfl
  have hinj : Function.Injective em := (WithAbs.equiv f).symm.injective.comp hinjK
  have hem0 : em π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have hpos : 0 < ‖em π‖ := norm_pos_iff.2 hem0
  have hle : ∀ x, ‖em x‖ ≤ 1 := fun x => (h _).2 ⟨x, rfl⟩
  have key : ∀ (n : ℕ) (x : R), x ∈ IsLocalRing.maximalIdeal R ^ n ↔ ‖em x‖ ≤ ‖em π‖ ^ n := by
    intro n x
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      rw [map_mul, map_pow, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hle y)
    · intro hx
      rw [hnorm, hnorm] at hx
      have hπK : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinjK).2 hπ.ne_zero
      obtain ⟨y, hy⟩ := (h (algebraMap R K x / algebraMap R K π ^ n)).1 (by
        rw [map_div₀, map_pow]
        exact div_le_one_of_le₀ hx (by positivity))
      refine ⟨y, hinjK ?_⟩
      rw [map_mul, map_pow, hy, mul_div_cancel₀ _ (pow_ne_zero _ hπK)]
  have hlt : ‖em π‖ < 1 := by
    by_contra hge
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R ^ 1 := (key 1 1).2 (by simpa using hge)
    rw [pow_one] at this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine Metric.complete_of_convergent_controlled_sequences (fun n => ‖em π‖ ^ n)
    (fun n => by positivity) ?_
  intro u hu
  have hv : ∀ n, ∃ v : R, em v = u n - u 0 := by
    intro n
    obtain ⟨v, hv⟩ := (h ((u n - u 0).ofAbs)).1 (by
      have := hu 0 n 0 (Nat.zero_le _) le_rfl
      rw [dist_eq_norm, pow_zero, WithAbs.norm_eq_apply_ofAbs] at this
      exact this.le)
    refine ⟨v, ?_⟩
    show WithAbs.toAbs f (algebraMap R K v) = _
    rw [hv, WithAbs.toAbs_ofAbs]
  choose v hv using hv
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal R) (M := R) inferInstance
    (f := v) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv, hv,
        sub_sub_sub_cancel_right]
      have := hu m m n le_rfl hmn
      rw [dist_eq_norm] at this
      exact this.le)
  refine ⟨em L + u 0, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt)
  have := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv] at this
  rw [dist_eq_norm]
  have e : u n - (em L + u 0) = u n - u 0 - em L := by abel
  rw [e]
  exact this

theorem exists_absoluteValue_completeSpace_of_isDiscreteValuationRing :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K] [Algebra R K]
      [IsFractionRing R K], ∃ f : AbsoluteValue K ℝ, IsNonarchimedean f ∧ f.IsNontrivial ∧
      (∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) ∧ CompleteSpace (WithAbs f) := by
  intro R K _ _ _ _ _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let v := IsDiscreteValuationRing.maximalIdeal R
  have hb : (1 : ℝ≥0) < 2 := one_lt_two
  have hball : ∀ x : K, v.adicAbv hb x ≤ 1 ↔ x ∈ Set.range (algebraMap R K) := by
    intro x
    have : v.adicAbv hb x ≤ 1 ↔ v.valuation K x ≤ 1 := by
      rw [← WithZeroMulInt.toNNReal_le_one_iff hb, ← NNReal.coe_le_coe]
      rfl
    rw [this]
    exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one,
      fun ⟨y, hy⟩ => hy ▸ v.valuation_le_one y⟩
  refine ⟨v.adicAbv hb, v.isNonarchimedean_adicAbv hb, ?_, hball,
    completeSpace_withAbs_of_unitBall R K _ hball⟩
  have hπK : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  have h1 : v.valuation K (algebraMap R K π) < 1 :=
    (v.valuation_lt_one_iff_mem π).2
      (show π ∈ IsLocalRing.maximalIdeal R from (IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)
  have h2 : WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) < 1 := by
    have := WithZeroMulInt.toNNReal_strictMono hb h1
    rwa [map_one] at this
  refine ⟨algebraMap R K π, hπK, ?_⟩
  intro heq
  have : ((WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) : ℝ≥0) : ℝ)
      = 1 := heq
  exact absurd (NNReal.coe_lt_coe.2 h2) (by rw [this]; simp)

end GlobalTheory.KLC

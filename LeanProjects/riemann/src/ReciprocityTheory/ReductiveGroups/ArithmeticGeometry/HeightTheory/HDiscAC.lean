import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.SemistableReduction.AlgAll

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscVal

open IsDedekindDomain WithZero ValPl

variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]

variable (O F) in
include F in

theorem addv_eq_of_mem {w : AddValuation L (WithTop ℤ)} (hw : w ∈ PlacesOver O L) :
    ∃ v : HeightOneSpectrum (integralClosure O L), w = addv L v := by
  obtain ⟨e, he⟩ := placesOver_bij O F L
  refine ⟨e.symm ⟨w, hw⟩, ?_⟩
  rw [← he, Equiv.apply_symm_apply]

variable (O F) in
include F in
theorem addv_mem (v : HeightOneSpectrum (integralClosure O L)) : addv L v ∈ PlacesOver O L := by
  have hval : ∀ y : L, y ≠ 0 →
      addv L v y = ((-WithZero.log (v.valuation L y) : ℤ) : WithTop ℤ) := by
    intro y hy
    unfold addv
    rw [AddValuation.of_apply, if_neg hy]
  have hP : v.asIdeal.comap (algebraMap O (integralClosure O L)) = IsLocalRing.maximalIdeal O := by
    haveI := v.isMaximal
    apply IsLocalRing.eq_maximalIdeal
    first
      | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
      | exact Ideal.IsMaximal.under O v.asIdeal
      | infer_instance
  simp only [PlacesOver, IsNormDiscrete, Set.mem_setOf_eq]
  refine ⟨⟨fun a ha => ?_, ?_⟩, fun x => ?_⟩
  · rw [hval a ha]
    exact WithTop.coe_ne_top
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact absurd hπ.symm (by simp)
    refine ⟨π, ?_⟩
    rw [hval π hπ0, hπ]
    first
      | simp
      | rfl
  · have hx : algebraMap O L x =
        algebraMap (integralClosure O L) L (algebraMap O (integralClosure O L) x) :=
      IsScalarTower.algebraMap_apply O (integralClosure O L) L x
    by_cases hx0 : algebraMap O L x = 0
    · have hx00 : x = 0 := by
        have h1 : algebraMap O F x = 0 := by
          apply (algebraMap F L).injective
          rw [← IsScalarTower.algebraMap_apply, map_zero]
          exact hx0
        exact IsFractionRing.injective O F (by rw [h1, map_zero])
      subst hx00
      simp
    · rw [hval _ hx0]
      have hv : v.valuation L (algebraMap O L x) ≠ 0 := by simpa using hx0
      have hle := WithZero.log_le_log hv one_ne_zero
      have hge := WithZero.log_le_log one_ne_zero hv
      rw [WithZero.log_one] at hle hge
      have hmem : v.valuation L (algebraMap O L x) < 1 ↔
          algebraMap O (integralClosure O L) x ∈ v.asIdeal := by
        rw [hx]
        first
          | exact v.valuation_lt_one_iff_mem _
          | exact v.valuation_lt_one_iff_mem L _
      have hint : v.valuation L (algebraMap O L x) ≤ 1 := by
        rw [hx]
        first
          | exact v.valuation_le_one _
          | exact v.valuation_le_one L _
      rw [← hP, Ideal.mem_comap, ← hmem]
      constructor
      · have h3 := hle.2 hint
        exact_mod_cast (show (0 : ℤ) ≤ -WithZero.log (v.valuation L (algebraMap O L x)) by omega)
      · constructor
        · intro h
          have h' : (0 : ℤ) < -WithZero.log (v.valuation L (algebraMap O L x)) := by
            exact_mod_cast h
          refine lt_of_le_of_ne hint (fun he => ?_)
          rw [he, WithZero.log_one] at h'
          omega
        · intro h
          have h1 : ¬ (0 ≤ WithZero.log (v.valuation L (algebraMap O L x))) :=
            fun h0 => (not_le.2 h) (hge.1 h0)
          have h2 : (0 : ℤ) < -WithZero.log (v.valuation L (algebraMap O L x)) := by omega
          exact_mod_cast h2

omit [IsFractionRing O F] [FiniteDimensional F L] [Algebra.IsSeparable F L] [IsScalarTower O F L] in

theorem addv_nonneg_iff (v : HeightOneSpectrum (integralClosure O L)) {y : L} (hy : y ≠ 0) :
    0 ≤ addv L v y ↔ v.valuation L y ≤ 1 := by
  have hv : v.valuation L y ≠ 0 := by simpa using hy
  have hval : addv L v y = ((-WithZero.log (v.valuation L y) : ℤ) : WithTop ℤ) := by
    unfold addv
    rw [AddValuation.of_apply, if_neg hy]
  rw [hval]
  have h2 := WithZero.log_le_log hv one_ne_zero
  rw [WithZero.log_one] at h2
  constructor
  · intro h
    have h' : (0 : ℤ) ≤ -WithZero.log (v.valuation L y) := by exact_mod_cast h
    exact h2.1 (by omega)
  · intro h
    have h' := h2.2 h
    have h'' : (0 : ℤ) ≤ -WithZero.log (v.valuation L y) := by omega
    exact_mod_cast h''

variable (O F) in
include F in
theorem mem_integralClosure_iff (y : L) :
    y ∈ integralClosure O L ↔ ∀ w ∈ PlacesOver O L, 0 ≤ w y := by
  constructor
  · intro hy w hw
    obtain ⟨v, rfl⟩ := addv_eq_of_mem O F hw
    by_cases hy0 : y = 0
    · subst hy0
      rw [AddValuation.map_zero]
      exact le_top
    · rw [addv_nonneg_iff v hy0]
      first
        | exact v.valuation_le_one (⟨y, hy⟩ : integralClosure O L)
        | exact v.valuation_le_one L (⟨y, hy⟩ : integralClosure O L)
  · intro h
    by_cases hy0 : y = 0
    · subst hy0
      exact Subalgebra.zero_mem _
    · have hle : ∀ v : HeightOneSpectrum (integralClosure O L), v.valuation L y ≤ 1 :=
        fun v => (addv_nonneg_iff v hy0).1 (h _ (addv_mem O F v))
      have hr : y ∈ (algebraMap (integralClosure O L) L).range := by
        first
          | exact HeightOneSpectrum.mem_integers_of_valuation_le_one L y hle
          | exact HeightOneSpectrum.mem_integers_of_valuation_le_one y hle
      obtain ⟨b, hb⟩ := hr
      rw [← hb]
      exact b.2

variable (O F) in
include F in

theorem exists_val_eq (n : AddValuation L (WithTop ℤ) → ℤ) :
    ∃ g : L, g ≠ 0 ∧ ∀ w ∈ PlacesOver O L, w g = n w := by
  classical
  obtain ⟨_, _, _, _, hmax, _⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F L
  haveI : IsPrincipalIdealRing (integralClosure O L) := IsPrincipalIdealRing.of_finite_maximals hmax
  haveI := hmax.to_subtype
  haveI : Finite (HeightOneSpectrum (integralClosure O L)) := by
    refine Finite.of_injective (fun v => (⟨v.asIdeal, v.isMaximal⟩ :
      {I : Ideal (integralClosure O L) | I.IsMaximal})) ?_
    intro v v' h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)
  letI := Fintype.ofFinite (HeightOneSpectrum (integralClosure O L))
  let π : HeightOneSpectrum (integralClosure O L) → integralClosure O L := fun v =>
    Submodule.IsPrincipal.generator v.asIdeal
  have hπ : ∀ v, v.asIdeal = Ideal.span {π v} := fun v =>
    (Ideal.span_singleton_generator v.asIdeal).symm
  have hπ0 : ∀ v, π v ≠ 0 := fun v h => v.ne_bot (by rw [hπ v, Ideal.span_singleton_eq_bot.mpr h])
  have hπL : ∀ v, algebraMap (integralClosure O L) L (π v) ≠ 0 := fun v =>
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosure O L) L)).mpr (hπ0 v)
  have hval : ∀ v v' : HeightOneSpectrum (integralClosure O L),
      v'.valuation L (algebraMap _ L (π v)) = if v' = v then exp (-1 : ℤ) else 1 := by
    intro v v'
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    split_ifs with h
    · subst h
      exact HeightOneSpectrum.intValuation_singleton _ (hπ0 v') (hπ v')
    · apply le_antisymm (v'.intValuation_le_one _)
      rw [← not_lt, v'.intValuation_lt_one_iff_mem]
      intro hmem
      apply h
      have hle : v.asIdeal ≤ v'.asIdeal := by
        rw [hπ v, Ideal.span_singleton_le_iff_mem]
        exact hmem
      exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle).symm
  let g : L := ∏ v, (algebraMap _ L (π v)) ^ (n (addv L v))
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (hπL v)
  have hgv : ∀ v' : HeightOneSpectrum (integralClosure O L), v'.valuation L g = exp (-(n (addv L v'))) := by
    intro v'
    simp only [g, map_prod, map_zpow₀, hval]
    rw [Finset.prod_eq_single v']
    · rw [if_pos rfl, ← exp_zsmul, smul_eq_mul, mul_neg_one]
    · intro v _ hv
      rw [if_neg (Ne.symm hv), one_zpow]
    · simp
  refine ⟨g, hg0, fun w hw => ?_⟩
  obtain ⟨v, rfl⟩ := addv_eq_of_mem O F hw
  rw [addv_apply v hg0, hgv, log_exp, neg_neg]

end HDiscVal

end ReciprocityTheory.ChartRestriction.G.T0

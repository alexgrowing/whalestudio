import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.NormLeOneOfInteger

namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

noncomputable def normAbv {l : ℕ} [Fact l.Prime] {E : Type} [Field E] (φ : E →+* Om l) :
    AbsoluteValue E ℝ where
  toFun x := ‖φ x‖
  map_mul' x y := by simp
  nonneg' x := norm_nonneg _
  eq_zero' x := by simp
  add_le' x y := by simpa using norm_add_le (φ x) (φ y)

theorem normAbv_apply {l : ℕ} [Fact l.Prime] {E : Type} [Field E] (φ : E →+* Om l) (x : E) :
    normAbv φ x = ‖φ x‖ := rfl

private lemma frac_lemma' {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (u : E)
    (hu : v.valuation E u ≤ 1) :
    ∃ c j : 𝓞 E, j ∉ v.asIdeal ∧ u = algebraMap (𝓞 E) E c / algebraMap (𝓞 E) E j := by
  classical
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) u
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d})).factors :=
    ⟨_, rfl⟩
  have hvd : v.intValuation d = WithZero.exp (-(k : ℤ)) := by
    rw [v.intValuation_if_neg hd0, hk]
  have hpos : 0 < v.intValuation d := by
    rw [hvd]; exact zero_lt_iff.mpr WithZero.exp_ne_zero
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    div_le_one₀ hpos, hvd] at hu
  have hdvda : v.asIdeal ^ k ∣ Ideal.span {a} := (v.intValuation_le_pow_iff_dvd a k).mp hu
  have hdvdd : v.asIdeal ^ k ∣ Ideal.span {d} := (v.intValuation_le_pow_iff_dvd d k).mp hvd.le
  obtain ⟨J, hJ⟩ := hdvdd
  have hJv : ¬ (J : Set (𝓞 E)) ⊆ v.asIdeal := by
    intro hle
    have h2 : v.asIdeal ^ (k + 1) ∣ Ideal.span {d} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr hle)
    have h3 := (v.intValuation_le_pow_iff_dvd d (k + 1)).mpr h2
    rw [hvd, WithZero.exp_le_exp] at h3
    push_cast at h3
    omega
  obtain ⟨j, hjJ, hjv⟩ := Set.not_subset.mp hJv
  have hmem : a * j ∈ Ideal.span {d} := by
    rw [hJ]
    exact Ideal.mul_mem_mul (Ideal.le_of_dvd hdvda (Ideal.mem_span_singleton_self a)) hjJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hj0 : j ≠ 0 := fun h => hjv (h ▸ v.asIdeal.zero_mem)
  have hjE : algebraMap (𝓞 E) E j ≠ 0 := fun h =>
    hj0 (IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero]))
  refine ⟨c, j, hjv, ?_⟩
  rw [div_eq_div_iff hdE hjE, ← map_mul, ← map_mul, hc]

private lemma le_one_lemma_2 {E : Type} [Field E] [NumberField E] (w : AbsoluteValue E ℝ)
    (v : HeightOneSpectrum (𝓞 E))
    (hw : ∀ x : 𝓞 E, w (algebraMap (𝓞 E) E x) ≤ 1 ∧ (w (algebraMap (𝓞 E) E x) < 1 ↔ x ∈ v.asIdeal))
    (u : E) : (v.valuation E u ≤ 1 ↔ w u ≤ 1) ∧ (v.valuation E u < 1 ↔ w u < 1) := by
  have hj1 : ∀ j : 𝓞 E, j ∉ v.asIdeal → w (algebraMap (𝓞 E) E j) = 1 := fun j hj =>
    le_antisymm (hw j).1 (not_lt.mp fun h => hj ((hw j).2.mp h))
  have hle : ∀ y : E, v.valuation E y ≤ 1 → w y ≤ 1 := by
    intro y hy
    obtain ⟨c, j, hj, rfl⟩ := frac_lemma' v y hy
    rw [map_div₀, hj1 j hj, div_one]
    exact (hw c).1
  have hlt : ∀ y : E, v.valuation E y < 1 → w y < 1 := by
    intro y hy
    obtain ⟨c, j, hj, rfl⟩ := frac_lemma' v y hy.le
    rw [map_div₀, hj1 j hj, div_one]
    apply (hw c).2.mpr
    have hj1' : v.intValuation j = 1 := le_antisymm (v.intValuation_le_one j)
      (not_lt.mp fun h => hj ((v.intValuation_lt_one_iff_mem j).mp h))
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      hj1', div_one] at hy
    exact (v.intValuation_lt_one_iff_mem c).mp hy
  by_cases hu0 : u = 0
  · subst hu0; simp
  have hnpos : 0 < w u := w.pos hu0
  constructor
  · refine ⟨hle u, fun h => ?_⟩
    by_contra hn
    push_neg at hn
    have h1 : v.valuation E u⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hn
    have h2 := hlt _ h1
    rw [map_inv₀] at h2
    exact absurd h (not_le.mpr ((inv_lt_one₀ hnpos).mp h2))
  · refine ⟨hlt u, fun h => ?_⟩
    by_contra hn
    push_neg at hn
    have h1 : v.valuation E u⁻¹ ≤ 1 := by rw [map_inv₀]; exact inv_le_one_of_one_le₀ hn
    have h2 := hle _ h1
    rw [map_inv₀] at h2
    exact absurd h (not_lt.mpr ((inv_le_one₀ hnpos).mp h2))

theorem isEquiv_adicAbv_normAbv {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ placesOver E l)
    (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ ≤ 1 ∧ (‖φ (x : E)‖ < 1 ↔ x ∈ v.asIdeal)) :
    (v.adicAbv (K := E) (b := 2) one_lt_two).IsEquiv (normAbv φ) := by
  rw [AbsoluteValue.isEquiv_iff_lt_one_iff]
  intro x
  rw [← (le_one_lemma_2 (normAbv φ) v (fun y => hφ y) x).2]
  exact (le_one_lemma_2 (v.adicAbv (K := E) (b := 2) one_lt_two) v
    (fun y => ⟨v.adicAbv_coe_le_one _ y, v.adicAbv_coe_lt_one_iff _ y⟩) x).2.symm

theorem intValuation_natCast {l : ℕ} [hl : Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ placesOver E l) :
    v.intValuation ((l : ℕ) : 𝓞 E) = WithZero.exp (-(v.asIdeal.ramificationIdx ℤ : ℤ)) := by
  classical
  have hl0 : ((l : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  rw [v.intValuation_if_neg hl0]
  suffices h : (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {((l : ℕ) : 𝓞 E)})).factors =
      v.asIdeal.ramificationIdx ℤ by rw [h]
  have hle : Ideal.span {((l : ℕ) : ℤ)} ≤ v.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hv
  have hunder : Ideal.span {((l : ℕ) : ℤ)} = v.asIdeal.under ℤ :=
    (Int.ideal_span_isMaximal_of_prime l).eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) hle
  haveI : v.asIdeal.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := ⟨hunder⟩
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((l : ℕ) : ℤ)}) =
      Ideal.span {((l : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hne : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {((l : ℕ) : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count _ _ hne, hmap,
    Ideal.count_associates_factors_eq (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
      v.isPrime v.ne_bot,
    UniqueFactorizationMonoid.factors_eq_normalizedFactors]

theorem kerProp : KerProp := by
  intro l _ E _ _ φ v hv hφ x
  have hl0 : ((l : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have key := (le_one_lemma_2 (normAbv φ) v (fun y => hφ y) (algebraMap (𝓞 E) E x / ((l : ℕ) : E))).1
  rw [← Ideal.dvd_span_singleton, ← v.intValuation_le_pow_iff_dvd, ← intValuation_natCast v hv]
  have hvl : 0 < v.intValuation ((l : ℕ) : 𝓞 E) := by
    rw [intValuation_natCast v hv]; exact zero_lt_iff.mpr WithZero.exp_ne_zero
  have hnl : 0 < ‖((l : ℕ) : Om l)‖ := by
    rw [← map_natCast φ]; exact norm_pos_iff.mpr ((map_ne_zero φ).mpr hl0)
  rw [← div_le_one₀ hvl, ← div_le_one hnl]
  have e1 : v.intValuation x / v.intValuation ((l : ℕ) : 𝓞 E) =
      v.valuation E (algebraMap (𝓞 E) E x / ((l : ℕ) : E)) := by
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, ← map_natCast (algebraMap (𝓞 E) E) l,
      HeightOneSpectrum.valuation_of_algebraMap]
  have e2 : ‖φ (x : E)‖ / ‖((l : ℕ) : Om l)‖ = normAbv φ (algebraMap (𝓞 E) E x / ((l : ℕ) : E)) := by
    rw [normAbv_apply, map_div₀, norm_div, map_natCast]
  rw [e1, e2]
  exact key.symm

end PI.CompDegEF

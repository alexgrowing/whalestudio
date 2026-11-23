import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst CrystallineSemistableComparison UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Seam

section Place

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

private theorem exists_den {x : E} (hx : w.valuation E x ≤ 1) :
    ∃ a b : 𝓞 E, b ∉ w.asIdeal ∧ x * algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E a := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd1 : algebraMap (𝓞 E) E d ≠ 0 := by simpa using hd0
  rw [map_div₀, div_le_one₀ (zero_lt_iff.2 (by simpa using hd1)), HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap] at hx
  set k := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {d})).factors with hk
  have hv : w.intValuation d = WithZero.exp (-(k : ℤ)) := w.intValuation_if_neg hd0
  have h1 : d ∈ w.asIdeal ^ k := (w.intValuation_le_pow_iff_mem d k).1 hv.le
  have h2 : n ∈ w.asIdeal ^ k := (w.intValuation_le_pow_iff_mem n k).1 (hx.trans hv.le)
  have h3 : d ∉ w.asIdeal ^ (k + 1) := fun h => by
    have := (w.intValuation_le_pow_iff_mem d (k + 1)).2 h
    rw [hv, WithZero.exp_le_exp] at this
    push_cast at this
    omega
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)
  have h4 : ¬ J ≤ w.asIdeal := fun h => h3 <| by
    have : d ∈ Ideal.span {d} := Ideal.mem_span_singleton_self d
    rw [hJ] at this
    rw [pow_succ]
    exact Ideal.mul_mono_right h this
  obtain ⟨b, hbJ, hb⟩ := SetLike.not_le_iff_exists.1 h4
  have h5 : n * b ∈ Ideal.span {d} := hJ ▸ Ideal.mul_mem_mul h2 hbJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h5
  refine ⟨a, b, hb, ?_⟩
  rw [div_mul_eq_mul_div, div_eq_iff hd1, ← map_mul, ← map_mul, ha]

private theorem mem_of_int (a : 𝓞 E) : algebraMap E Ω (algebraMap (𝓞 E) E a) ∈ A := by
  have h : IsIntegral A (algebraMap E Ω (algebraMap (𝓞 E) E a)) :=
    ((RingOfIntegers.isIntegral_coe a).algebraMap (B := Ω)).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

private theorem val_eq_one (hA : IsPlaceOver A w) {b : 𝓞 E} (hb : b ∉ w.asIdeal) :
    A.valuation (algebraMap E Ω (algebraMap (𝓞 E) E b)) = 1 :=
  le_antisymm ((A.valuation_le_one_iff _).2 (mem_of_int b)) (not_lt.1 fun h => hb ((hA b).1 h))

private theorem mem_of_le_one (hA : IsPlaceOver A w) {x : E} (hx : w.valuation E x ≤ 1) :
    algebraMap E Ω x ∈ A := by
  obtain ⟨a, b, hb, e⟩ := exists_den hx
  rw [← A.valuation_le_one_iff]
  have h := congrArg (fun y => A.valuation (algebraMap E Ω y)) e
  simp only [map_mul, val_eq_one hA hb, mul_one] at h
  rw [h]
  exact (A.valuation_le_one_iff _).2 (mem_of_int a)

private theorem val_lt_one (hA : IsPlaceOver A w) {x : E} (hx : w.valuation E x < 1) :
    A.valuation (algebraMap E Ω x) < 1 := by
  obtain ⟨a, b, hb, e⟩ := exists_den hx.le
  have hb1 : w.valuation E (algebraMap (𝓞 E) E b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hb ((w.valuation_lt_one_iff_mem b).1 h))
  have ha : a ∈ w.asIdeal := by
    rw [← w.valuation_lt_one_iff_mem (K := E)]
    change w.valuation E (algebraMap (𝓞 E) E a) < 1
    rw [← e, map_mul, hb1, mul_one]
    exact hx
  have h := congrArg (fun y => A.valuation (algebraMap E Ω y)) e
  simp only [map_mul, val_eq_one hA hb, mul_one] at h
  rw [h]
  exact (hA a).2 ha

private theorem le_one_of_mem (hA : IsPlaceOver A w) {x : E} (hx : algebraMap E Ω x ∈ A) :
    w.valuation E x ≤ 1 := by
  by_contra h
  have h1 : 1 < w.valuation E x := not_le.1 h
  have h0 : w.valuation E x ≠ 0 := (zero_lt_one.trans h1).ne'
  have h2 : w.valuation E x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h1
  have h3 := val_lt_one hA h2
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at h0
  have h4 : A.valuation (algebraMap E Ω x) ≠ 0 := by simpa using hx0
  rw [map_inv₀, map_inv₀, inv_lt_one₀ (zero_lt_iff.2 h4)] at h3
  exact absurd ((A.valuation_le_one_iff _).2 hx) (not_le.2 h3)

end Place

private theorem mem_OK_iff {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (x : ↥K) :
    x ∈ OK l K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  GroundTheory.PAdicHodge.mem_normInteger

private theorem isUnit_OK_iff {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (y : ↥(OK l K)) :
    IsUnit y ↔ ‖((y : ↥K) : PadicAlgCl l)‖ = 1 := by
  have hmul : ∀ a b : ↥(OK l K), ‖(((a * b : ↥(OK l K)) : ↥K) : PadicAlgCl l)‖ =
      ‖((a : ↥K) : PadicAlgCl l)‖ * ‖((b : ↥K) : PadicAlgCl l)‖ := fun a b => norm_mul _ _
  have hle : ∀ a : ↥(OK l K), ‖((a : ↥K) : PadicAlgCl l)‖ ≤ 1 := fun a => (mem_OK_iff _).1 a.2
  constructor
  · rintro ⟨u, rfl⟩
    have h := hmul u (↑u⁻¹ : ↥(OK l K))
    rw [Units.mul_inv] at h
    have h1 : ‖(((1 : ↥(OK l K)) : ↥K) : PadicAlgCl l)‖ = 1 := norm_one
    rw [h1] at h
    have h2 := hle u
    have h3 := hle (↑u⁻¹ : ↥(OK l K))
    have h4 := norm_nonneg (((u : ↥(OK l K)) : ↥K) : PadicAlgCl l)
    nlinarith
  · intro h
    have hy0 : (y : ↥K) ≠ 0 := fun h0 => by
      rw [h0] at h
      simp at h
    have hinv : (y : ↥K)⁻¹ ∈ OK l K := by
      rw [mem_OK_iff]
      change ‖((y : ↥K) : PadicAlgCl l)⁻¹‖ ≤ 1
      rw [norm_inv, h, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hy0))

theorem intMap : IntMap := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hj
  haveI : IsDiscreteValuationRing (Ow w) := (w.valuation E).valuationSubring_isDiscreteValuationRing
  have hmem : ∀ x : Ow w, algebraMap E Ω (algebraMap (Ow w) E x) ∈ A := fun x =>
    mem_of_le_one hA ((Valuation.mem_valuationSubring_iff _ _).1 x.2)
  have hφ : ∀ x : Ow w, ((kOf Bw).comp (algebraMap (Ow w) E)) x ∈ OK l Bw.Kw.1 := fun x =>
    (mem_OK_iff _).2 ((hj _).1 (hmem x))
  refine ⟨((kOf Bw).comp (algebraMap (Ow w) E)).codRestrict (OK l Bw.Kw.1) hφ, fun x => rfl, fun ϖ hϖ => ?_⟩
  let ν : Ow w → ℝ := fun x => ‖Bw.j (algebraMap E Ω (algebraMap (Ow w) E x))‖
  let M : ↥(OK l Bw.Kw.1) → ℝ := fun y => ‖((y : ↥Bw.Kw.1) : PadicAlgCl l)‖
  have hν1 : ∀ x, ν x ≤ 1 := fun x => (hj _).1 (hmem x)
  have hνmul : ∀ x y, ν (x * y) = ν x * ν y := fun x y => by simp only [ν, map_mul, norm_mul]
  have hϖ0 : (algebraMap (Ow w) E ϖ) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hϖw : w.valuation E (algebraMap (Ow w) E ϖ) < 1 := by
    by_contra h
    have h1 : w.valuation E (algebraMap (Ow w) E ϖ) = 1 :=
      le_antisymm ((Valuation.mem_valuationSubring_iff _ _).1 ϖ.2) (not_lt.1 h)
    have hinv : (algebraMap (Ow w) E ϖ)⁻¹ ∈ (w.valuation E).valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff, map_inv₀, h1, inv_one]
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hϖ0)))
  have hϖ1 : ν ϖ < 1 := (Induces.valuation_lt_one_iff hj _).1 (val_lt_one hA hϖw)
  have hϖp : 0 < ν ϖ := norm_pos_iff.2 ((map_ne_zero _).2 ((map_ne_zero _).2 hϖ0))
  have hbound : ∀ y : ↥(OK l Bw.Kw.1), M y < 1 → 0 < M y → M y ≤ ν ϖ := by
    intro y hy hpos
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (Bw.j_dense (y : ↥Bw.Kw.1).2) _ hpos
    rw [dist_eq_norm] at hx
    set t : PadicAlgCl l := Bw.j (algebraMap E Ω x) with ht
    set s : PadicAlgCl l := ((y : ↥Bw.Kw.1) : PadicAlgCl l) with hs
    have hM : M y = ‖s‖ := rfl
    rw [hM] at hy hpos ⊢
    have h1 : ‖t‖ ≤ ‖s‖ := by
      have h := IsUltrametricDist.norm_add_le_max s (t - s)
      rw [add_sub_cancel, norm_sub_rev] at h
      exact h.trans (max_le le_rfl hx.le)
    have h2 : ‖s‖ ≤ ‖t‖ := by
      have h := IsUltrametricDist.norm_add_le_max t (s - t)
      rw [add_sub_cancel] at h
      exact (le_max_iff.1 h).resolve_right (not_le.2 hx)
    have hxw : w.valuation E x ≤ 1 := le_one_of_mem hA ((hj _).2 (h1.trans hy.le))
    let ξ : Ow w := ⟨x, (Valuation.mem_valuationSubring_iff _ _).2 hxw⟩
    have hξ : ν ξ = ‖t‖ := rfl
    have hnu : ¬ IsUnit ξ := by
      rintro ⟨u, hu⟩
      have h3 := hνmul u (↑u⁻¹ : Ow w)
      rw [Units.mul_inv, hu, hξ] at h3
      have h4 : ν 1 = 1 := by simp [ν]
      rw [h4] at h3
      have h5 := hν1 (↑u⁻¹ : Ow w)
      have h6 := norm_nonneg t
      nlinarith
    have hmax : ξ ∈ Ideal.span {ϖ} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
      exact (IsLocalRing.mem_maximalIdeal ξ).2 hnu
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmax
    have h3 : ν ξ = ν c * ν ϖ := by rw [← hc, hνmul]
    have h4 := hν1 c
    have h5 : ‖t‖ ≤ ν ϖ := by
      rw [← hξ, h3]
      nlinarith
    exact h2.trans h5
  set φ := ((kOf Bw).comp (algebraMap (Ow w) E)).codRestrict (OK l Bw.Kw.1) hφ with hφdef
  have hMϖ : M (φ ϖ) = ν ϖ := rfl
  have hMmul : ∀ a b, M (a * b) = M a * M b := fun a b => norm_mul _ _
  have hMle : ∀ a, M a ≤ 1 := fun a => (mem_OK_iff _).1 a.2
  rw [irreducible_iff]
  refine ⟨fun h => ?_, fun a b hab => ?_⟩
  · have := (isUnit_OK_iff _).1 h
    change M (φ ϖ) = 1 at this
    rw [hMϖ] at this
    exact hϖ1.ne this
  · by_contra hn
    obtain ⟨ha, hb⟩ := not_or.1 hn
    have ha1 : M a < 1 := lt_of_le_of_ne (hMle a) fun h => ha ((isUnit_OK_iff _).2 h)
    have hb1 : M b < 1 := lt_of_le_of_ne (hMle b) fun h => hb ((isUnit_OK_iff _).2 h)
    have hprod : ν ϖ = M a * M b := by rw [← hMϖ, hab, hMmul]
    have ha0 : 0 ≤ M a := norm_nonneg _
    have hb0 : 0 ≤ M b := norm_nonneg _
    have hap : 0 < M a := lt_of_le_of_ne ha0 fun h => by
      rw [← h, zero_mul] at hprod
      exact hϖp.ne' hprod
    have hbp : 0 < M b := lt_of_le_of_ne hb0 fun h => by
      rw [← h, mul_zero] at hprod
      exact hϖp.ne' hprod
    have h1 := hbound a ha1 hap
    have h2 := hbound b hb1 hbp
    have h3 : M a * M b ≤ ν ϖ * ν ϖ := mul_le_mul h1 h2 hb0 hϖp.le
    nlinarith

end UpperTheory.Gal.Seam

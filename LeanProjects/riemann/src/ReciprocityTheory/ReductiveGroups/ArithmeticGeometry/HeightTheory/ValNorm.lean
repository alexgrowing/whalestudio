import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValPlRes
import ReciprocityTheory.SemistableReduction.AlgAll

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace ValPl

open IsDedekindDomain IsLocalRing

variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]

variable (O F L) in

noncomputable def hoEquiv : HeightOneSpectrum (integralClosure O L) ≃
    {Q : Ideal (integralClosure O L) // Q.IsMaximal} where
  toFun v := ⟨v.asIdeal, v.isMaximal⟩
  invFun Q := (exists_heightOne O F L Q.1 Q.2).choose
  left_inv v := by
    apply HeightOneSpectrum.ext
    exact (exists_heightOne O F L v.asIdeal v.isMaximal).choose_spec
  right_inv Q := Subtype.ext (exists_heightOne O F L Q.1 Q.2).choose_spec

include F in

theorem norm_integral (b : integralClosure O L) (hb : b ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F (algebraMap (integralClosure O L) L b) = algebraMap O F
        (ϖ ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O *
          Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})))
          * u) := by
  haveI : Module.Finite O (integralClosure O L) :=
    IsIntegralClosure.finite O F L (integralClosure O L)
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  have hinjB : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro x y hxy
    apply hinj
    rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L x,
      IsScalarTower.algebraMap_apply O (integralClosure O L) L y, hxy]
  haveI : NoZeroSMulDivisors O (integralClosure O L) := by
    refine ⟨fun {c x} h => ?_⟩
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left (fun h' => hinjB (h'.trans (map_zero _).symm))
  have hN := ReciprocityTheory.MultiplicativeHeights.Closed.normOrd O (integralClosure O L) b hb
  have hne : Algebra.norm O b ≠ 0 := by
    intro h0
    rw [h0, IsDiscreteValuationRing.addVal_zero] at hN
    exact ENat.top_ne_coe _ hN
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hn := IsDiscreteValuationRing.addVal_def _ u hϖ n hu
  rw [hn] at hN
  have hnN : n = ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}, Q.1.inertiaDeg O *
      Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
    exact_mod_cast hN
  have hsum : (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O *
      Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) = n := by
    rw [hnN]
    exact finsum_comp_equiv (hoEquiv O F L)
      (f := fun Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal} => Q.1.inertiaDeg O *
        Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})))
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure O L) (nonZeroDivisors O)) L :=
    IsIntegralClosure.isLocalization O F L (integralClosure O L)
  refine ⟨u, u.isUnit, ?_⟩
  rw [Algebra.norm_localization O (nonZeroDivisors O) b, hu, hsum, mul_comm (u : O)]

theorem norm_eq_heightOne (y : L) (hy : y ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F y = (algebraMap O F ϖ) ^
        (∑ᶠ v : HeightOneSpectrum (integralClosure O L),
          (v.asIdeal.inertiaDeg O : ℤ) * WithTop.untopD 0 (addv L v y)) * algebraMap O F u := by
  haveI : Finite (HeightOneSpectrum (integralClosure O L)) := by
    have hinj : Function.Injective (algebraMap O L) := by
      rw [IsScalarTower.algebraMap_eq O F L]
      exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
    obtain ⟨b, hbdef⟩ : ∃ b : (integralClosure O L), b = algebraMap O (integralClosure O L) ϖ := ⟨_, rfl⟩
    have hbL : algebraMap (integralClosure O L) L b = algebraMap O L ϖ := by
      rw [hbdef]
      exact (IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ).symm
    have hb : b ≠ 0 := by
      intro h0
      have h00 : algebraMap O L ϖ = 0 := by rw [← hbL, h0, map_zero]
      exact hϖ.ne_zero (hinj (h00.trans (map_zero _).symm))
    have hmem : ϖ ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
    have hdvd : ∀ v : HeightOneSpectrum (integralClosure O L), v.asIdeal ∣ Ideal.span {b} := by
      intro v
      have h1 := ((addv_mem_placesOver (O := O) (L := L) v).2 ϖ).2.2 hmem
      rw [← hbL, addv_count v b hb] at h1
      have h2 : 0 < Multiset.count v.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
        rcases Nat.eq_zero_or_pos (Multiset.count v.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) with h | h
        · rw [h, Nat.cast_zero] at h1
          exact absurd h1 (lt_irrefl 0)
        · exact h
      exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.count_pos.1 h2)
    have hspan : Ideal.span {b} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hb
    have hfin := Ideal.finite_factors hspan
    have huniv : {v : HeightOneSpectrum (integralClosure O L) | v.asIdeal ∣ Ideal.span {b}} = Set.univ :=
      Set.eq_univ_of_forall hdvd
    rw [huniv] at hfin
    exact Set.finite_univ_iff.1 hfin
  haveI := Fintype.ofFinite (HeightOneSpectrum (integralClosure O L))
  obtain ⟨b1, b2, hb2m, hyb⟩ := IsFractionRing.div_surjective (A := (integralClosure O L)) y
  have hb2 : b2 ≠ 0 := nonZeroDivisors.ne_zero hb2m
  have hb1 : b1 ≠ 0 := by
    intro h
    apply hy
    rw [← hyb, h, map_zero, zero_div]
  have hb2L : algebraMap (integralClosure O L) L b2 ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosure O L) L)).2 hb2
  have hyb2 : y * algebraMap (integralClosure O L) L b2 = algebraMap (integralClosure O L) L b1 := by
    rw [← hyb, div_mul_cancel₀ _ hb2L]
  have ha : algebraMap O F ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O F)).2 hϖ.ne_zero
  obtain ⟨u1, hu1, h1⟩ := norm_integral (F := F) b1 hb1 hϖ
  obtain ⟨u2, hu2, h2⟩ := norm_integral (F := F) b2 hb2 hϖ
  have hmul : Algebra.norm F y * Algebra.norm F (algebraMap (integralClosure O L) L b2) =
      Algebra.norm F (algebraMap (integralClosure O L) L b1) := by
    rw [← map_mul, hyb2]
  rw [h1, h2] at hmul
  simp only [map_mul, map_pow] at hmul
  have hk : ∀ v : HeightOneSpectrum (integralClosure O L),
      WithTop.untopD 0 (addv L v y) = ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1})) : ℕ) : ℤ) - ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2})) : ℕ) : ℤ) := by
    intro v
    have hm := (addv L v).map_mul y (algebraMap (integralClosure O L) L b2)
    rw [hyb2, addv_count v b1 hb1, addv_count v b2 hb2] at hm
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (mt (addv L v).top_iff.1 hy)
    rw [← hk] at hm ⊢
    have hm' : ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1})) : ℕ) : ℤ) = k + ((Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2})) : ℕ) : ℤ) := by
      exact_mod_cast hm
    rw [WithTop.untopD_coe]
    omega
  have hz : (∑ᶠ v : HeightOneSpectrum (integralClosure O L),
      (v.asIdeal.inertiaDeg O : ℤ) * WithTop.untopD 0 (addv L v y)) =
        (((∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1}))) : ℕ) : ℤ) - (((∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) : ℕ) : ℤ) := by
    simp only [hk]
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  refine ⟨u1 * ((hu2.unit⁻¹ : Oˣ) : O), hu1.mul (hu2.unit⁻¹).isUnit, ?_⟩
  have hU : algebraMap O F u2 * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, hu2.mul_val_inv, map_one]
  have haS : (algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) ≠ 0 := pow_ne_zero _ ha
  rw [hz, zpow_sub₀ ha, zpow_natCast, zpow_natCast, map_mul]
  calc Algebra.norm F y
      = Algebra.norm F y * ((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))) * algebraMap O F u2) *
          (((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))))⁻¹ * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O)) := by
        rw [mul_assoc, mul_mul_mul_comm, mul_inv_cancel₀ haS, hU, one_mul, mul_one]
    _ = (algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b1}))) * algebraMap O F u1 *
          (((algebraMap O F ϖ) ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O * Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b2}))))⁻¹ * algebraMap O F ((hu2.unit⁻¹ : Oˣ) : O)) := by
        rw [hmul]
    _ = _ := by
        rw [div_eq_mul_inv]
        ring

theorem norm_eq_places (y : L) (hy : y ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F y = (algebraMap O F ϖ) ^
        (∑ᶠ (w : AddValuation L (WithTop ℤ)) (_ : w ∈ PlacesOver O L),
          (letI := resAlg (F := F) w
           (Module.finrank (ResidueField ((vRing w).comap (algebraMap F L)))
             (ResidueField (vRing w)) : ℤ)) * WithTop.untopD 0 (w y)) * algebraMap O F u := by
  obtain ⟨u, hu, h⟩ := norm_eq_heightOne (F := F) y hy hϖ
  refine ⟨u, hu, ?_⟩
  rw [h]
  congr 2
  obtain ⟨e, he⟩ := placesOver_bij (O := O) (F := F) (L := L)
  rw [← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv e]
  apply finsum_congr
  intro v
  rw [he v]
  congr 1
  exact congrArg (fun n : ℕ => (n : ℤ)) (resDeg_addv (F := F) v).symm

variable (O L) in
include F in

theorem placesOver_finite : (PlacesOver O L).Finite := by
  obtain ⟨e, -⟩ := placesOver_bij (O := O) (F := F) (L := L)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  obtain ⟨b, hbdef⟩ : ∃ b : integralClosure O L, b = algebraMap O (integralClosure O L) ϖ :=
    ⟨_, rfl⟩
  have hbL : algebraMap (integralClosure O L) L b = algebraMap O L ϖ := by
    rw [hbdef]
    exact (IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ).symm
  have hb : b ≠ 0 := by
    intro h0
    have h00 : algebraMap O L ϖ = 0 := by rw [← hbL, h0, map_zero]
    exact hϖ.ne_zero (hinj (h00.trans (map_zero _).symm))
  have hmem : ϖ ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hdvd : ∀ v : HeightOneSpectrum (integralClosure O L), v.asIdeal ∣ Ideal.span {b} := by
    intro v
    have h1 := ((addv_mem_placesOver (O := O) (L := L) v).2 ϖ).2.2 hmem
    rw [← hbL, addv_count v b hb] at h1
    have h2 : 0 < Multiset.count v.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
      rcases Nat.eq_zero_or_pos (Multiset.count v.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) with h | h
      · rw [h, Nat.cast_zero] at h1
        exact absurd h1 (lt_irrefl 0)
      · exact h
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.count_pos.1 h2)
  have hspan : Ideal.span {b} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hb
  have hfin := Ideal.finite_factors hspan
  have hfin' : Finite (HeightOneSpectrum (integralClosure O L)) := by
    have huniv : {v : HeightOneSpectrum (integralClosure O L) | v.asIdeal ∣ Ideal.span {b}} =
        Set.univ := Set.eq_univ_of_forall hdvd
    rw [huniv] at hfin
    exact Set.finite_univ_iff.1 hfin
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ e)

end ValPl

end ReciprocityTheory.ChartRestriction.G.T0

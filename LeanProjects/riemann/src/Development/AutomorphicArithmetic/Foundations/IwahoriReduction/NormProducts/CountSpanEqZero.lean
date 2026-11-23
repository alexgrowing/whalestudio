import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfPowEqSpanStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisorDescentModUnramifiedGaloisSubmodule

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

private theorem valuation_eq_exp_neg_count_spanSingleton {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (v : IsDedekindDomain.HeightOneSpectrum R) {x : L}
    (hx : x ≠ 0) :
    v.valuation L x = WithZero.exp
      (-FractionalIdeal.count L v (FractionalIdeal.spanSingleton (nonZeroDivisors R) x)) := by
  classical
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hs : (s : R) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors R) (IsLocalization.mk' L a s) =
      FractionalIdeal.spanSingleton (nonZeroDivisors R) ((algebraMap R L) (s : R))⁻¹ *
        ↑(Ideal.span {a}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_inv_mul]
  rw [FractionalIdeal.count_well_defined L v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    hspan, IsDedekindDomain.HeightOneSpectrum.valuation_of_mk', v.intValuation_if_neg ha,
    v.intValuation_if_neg hs, ← WithZero.exp_sub]
  congr 1
  ring

private theorem valuation_eq_one_of_valuationSubring_eq_one {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (v : IsDedekindDomain.HeightOneSpectrum R) {y : L}
    (hy : ((v.valuation L).valuationSubring).valuation y = 1) : v.valuation L y = 1 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have h1 : y ∈ (v.valuation L).valuationSubring :=
    (ValuationSubring.valuation_le_one_iff _ y).mp hy.le
  have h2 : y⁻¹ ∈ (v.valuation L).valuationSubring :=
    (ValuationSubring.valuation_le_one_iff _ _).mp (by rw [map_inv₀, hy, inv_one])
  rw [Valuation.mem_valuationSubring_iff] at h1 h2
  rw [map_inv₀] at h2
  have hv0 : v.valuation L y ≠ 0 := by simpa using hy0
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr hv0)).mp h2)

private theorem ringOfIntegers_mem_of_polynomial_mem (k K : Type) [Field k] [Field K] [Algebra k[X] K]
    [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K] (B : ValuationSubring K)
    (hB : ∀ p : k[X], algebraMap k[X] K p ∈ B) (x : FunctionField.ringOfIntegers k K) :
    (x : K) ∈ B := by
  obtain ⟨p, hpm, hp⟩ := x.2
  let φ : k[X] →+* B := (algebraMap k[X] K).codRestrict B hB
  have hc : (algebraMap B K).comp φ = algebraMap k[X] K := RingHom.ext fun _ => rfl
  have hint : IsIntegral B (x : K) := by
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hc]
    exact hp
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

private theorem exists_mul_spanSingleton_eq_of_classGroup_mk_eq {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (I J : (FractionalIdeal (nonZeroDivisors R) L)ˣ)
    (h : ClassGroup.mk L I = ClassGroup.mk L J) :
    ∃ x : L, x ≠ 0 ∧
      (I : FractionalIdeal (nonZeroDivisors R) L) * FractionalIdeal.spanSingleton (nonZeroDivisors R) x = J := by
  have h2 := congrArg (ClassGroup.equiv L) h
  rw [ClassGroup.equiv_mk, ClassGroup.equiv_mk, QuotientGroup.mk'_eq_mk'] at h2
  obtain ⟨z, ⟨x, rfl⟩, hz⟩ := h2
  refine ⟨x, x.ne_zero, ?_⟩
  have h3 := congrArg Units.val hz
  simpa [FractionalIdeal.canonicalEquiv_self] using h3

theorem UpperTheory.Kd.K4.cdAbs :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (m m' : ℕ) (f : K), 0 < m → 0 < m' → f ≠ 0 →
      (∀ B : ValuationSubring K, (∀ p : k[X], algebraMap k[X] K p ∈ B) → ∃ c : K, c ≠ 0 ∧ B.valuation (f / c ^ m) = 1) →
      ∃ h : K, h ≠ 0 ∧ ∀ B : ValuationSubring K, (∀ p : k[X], algebraMap k[X] K p ∈ B) → ∃ c : K, c ≠ 0 ∧ B.valuation (f / h ^ m / c ^ (m * m')) = 1 := by
  intro k K _ _ _ _ _ _ _ _ m m' f hm hm' hf hloc
  classical
  have hF : FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf
  have hdiv : ∀ v : IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k K),
      (m : ℤ) ∣ FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f) := by
    intro v
    obtain ⟨c, hc, hcv⟩ := hloc ((v.valuation K).valuationSubring) (fun p => by
      rw [Valuation.mem_valuationSubring_iff,
        IsScalarTower.algebraMap_apply k[X] (FunctionField.ringOfIntegers k K) K]
      exact v.valuation_le_one _)
    have h1 := valuation_eq_one_of_valuationSubring_eq_one v hcv
    have hc0 : v.valuation K c ^ m ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hc)
    rw [map_div₀, map_pow, div_eq_one_iff_eq hc0, valuation_eq_exp_neg_count_spanSingleton v hf, valuation_eq_exp_neg_count_spanSingleton v hc,
      ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h1
    exact ⟨FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ c), by linarith⟩
  obtain ⟨I, hIdef⟩ : ∃ I : FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K,
      I = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k K),
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K) ^
          (FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f) / m) :=
    ⟨_, rfl⟩
  have he : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (FunctionField.ringOfIntegers k K) in
      Filter.cofinite, FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (FunctionField.ringOfIntegers k K)) f) / m = 0 :=
    (FractionalIdeal.finite_factors _).mono fun v hv => by rw [hv, Int.zero_ediv]
  have hI0 : I ≠ 0 := by
    rw [hIdef]
    refine finprod_induction (fun J => J ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) ?_
    intro v
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  have hIm : I ^ m = FractionalIdeal.spanSingleton _ f := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (pow_ne_zero m hI0)]
    conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hF]
    refine finprod_congr fun v => ?_
    rw [FractionalIdeal.count_pow, hIdef, FractionalIdeal.count_finprod K v _ he,
      Int.mul_ediv_cancel' (hdiv v)]
  obtain ⟨d, hd⟩ := GlobalTheory.T.classGroup_affineCurve_divisible_charZero k K m' hm' (ClassGroup.mk K (Units.mk0 I hI0))
  obtain ⟨Ju, rfl⟩ : ∃ Ju : (FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K)ˣ,
      ClassGroup.mk K Ju = d :=
    ClassGroup.induction K (P := fun d => ∃ Ju, ClassGroup.mk K Ju = d) (fun J => ⟨J, rfl⟩) d
  rw [← map_pow] at hd
  obtain ⟨x, hx, hxJ⟩ := exists_mul_spanSingleton_eq_of_classGroup_mk_eq _ _ hd
  rw [Units.val_mk0, Units.val_pow_eq_pow_val] at hxJ
  refine ⟨x⁻¹, inv_ne_zero hx, fun B hB => ?_⟩
  have hJ : ((Ju : FractionalIdeal (nonZeroDivisors (FunctionField.ringOfIntegers k K)) K) :
      Submodule (FunctionField.ringOfIntegers k K) K) ^ (m * m') =
        (FunctionField.ringOfIntegers k K) ∙ (f / x⁻¹ ^ m) := by
    rw [← FractionalIdeal.coe_pow, ← FractionalIdeal.coe_spanSingleton (nonZeroDivisors _), pow_mul',
      ← hxJ, mul_pow, hIm, FractionalIdeal.spanSingleton_pow,
      FractionalIdeal.spanSingleton_mul_spanSingleton, inv_pow, div_inv_eq_mul]
  have hw : f / x⁻¹ ^ m ≠ 0 := div_ne_zero hf (pow_ne_zero _ (inv_ne_zero hx))
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.exists_valuation_div_pow_eq_one_of_pow_eq_span K K (FunctionField.ringOfIntegers k K) B _ (m * m')
    (Nat.mul_pos hm hm') (fun r => ringOfIntegers_mem_of_polynomial_mem k K B hB r) (f / x⁻¹ ^ m) hw hJ
  exact ⟨c, hc, by simpa using hcv⟩

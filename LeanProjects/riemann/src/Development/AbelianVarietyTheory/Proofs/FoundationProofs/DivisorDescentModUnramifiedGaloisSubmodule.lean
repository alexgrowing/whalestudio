import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

open IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.DivisorDescent

open IsDedekindDomain in
open scoped nonZeroDivisors Pointwise in

theorem _root_.GlobalTheory.DivisorDescent.exists_pow_eq_of_dvd_count {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] (N : ℕ) (I : FractionalIdeal R⁰ L) (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, (N : ℤ) ∣ FractionalIdeal.count L v I) :
    ∃ J : FractionalIdeal R⁰ L, J ^ N = I := by
  classical
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum R =>
      (v.asIdeal : FractionalIdeal R⁰ L) ^ (FractionalIdeal.count L v I / N)).Finite := by
    refine (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := L) I)).subset ?_
    intro v hv
    rw [Function.mem_mulSupport] at hv
    intro h0
    apply hv
    simp [h0]
  refine ⟨∏ᶠ v : HeightOneSpectrum R,
    (v.asIdeal : FractionalIdeal R⁰ L) ^ (FractionalIdeal.count L v I / N), ?_⟩
  rw [finprod_pow hfin]
  conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' L hI]
  refine finprod_congr fun v => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, Int.mul_ediv_cancel' (h v)]

open IsDedekindDomain in
open scoped nonZeroDivisors Pointwise in

theorem _root_.GlobalTheory.DivisorDescent.exists_pow_class {A : Type} [CommRing A]
    [IsDedekindDomain A] (N : ℕ)
    (hCl : ∀ c : ClassGroup A, ∃ d, c = d ^ N) (a : Ideal A) (ha : a ≠ ⊥) :
    ∃ (b : Ideal A) (x y : A), b ≠ ⊥ ∧ x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {x} * a = Ideal.span {y} * b ^ N := by
  have ha' : a ∈ (Ideal A)⁰ := mem_nonZeroDivisors_of_ne_zero ha
  obtain ⟨d, hd⟩ := hCl (ClassGroup.mk0 ⟨a, ha'⟩)
  obtain ⟨b, rfl⟩ := ClassGroup.mk0_surjective d
  rw [← map_pow, ClassGroup.mk0_eq_mk0_iff] at hd
  obtain ⟨x, y, hx, hy, hxy⟩ := hd
  exact ⟨b, x, y, nonZeroDivisors.coe_ne_zero b, hx, hy, by simpa using hxy⟩

open IsDedekindDomain in
open scoped nonZeroDivisors Pointwise in
private theorem exists_galois_comap_eq_of_comap_eq {A₀ R K₀ L : Type} [CommRing A₀]
    [IsDedekindDomain A₀] [CommRing R] [IsDedekindDomain R] [Field K₀] [Field L]
    [Algebra A₀ K₀] [IsFractionRing A₀ K₀] [Algebra R L] [IsFractionRing R L] [Algebra A₀ R]
    [Algebra K₀ L] [Algebra A₀ L]
    [IsScalarTower A₀ R L] [IsScalarTower A₀ K₀ L] [IsIntegralClosure R A₀ L]
    [FiniteDimensional K₀ L] [IsGalois K₀ L] (v v' : HeightOneSpectrum R)
    (h : v.asIdeal.comap (algebraMap A₀ R) = v'.asIdeal.comap (algebraMap A₀ R)) :
    ∃ σ : L ≃ₐ[K₀] L, v'.asIdeal = Ideal.comap (galRestrict A₀ K₀ L R σ).toRingEquiv v.asIdeal := by
  letI := IsIntegralClosure.MulSemiringAction A₀ K₀ L R
  haveI : Algebra.IsIntegral A₀ R := IsIntegralClosure.isIntegral_algebra A₀ L
  haveI : IsGaloisGroup (L ≃ₐ[K₀] L) A₀ R := IsGaloisGroup.of_isFractionRing _ A₀ R K₀ L
  have hpre := Ideal.isPretransitive_of_isGaloisGroup (v.asIdeal.comap (algebraMap A₀ R)) (L ≃ₐ[K₀] L) (B := R)
  have h1 : v.asIdeal ∈ (v.asIdeal.comap (algebraMap A₀ R)).primesOver R :=
    ⟨v.isPrime, ⟨rfl⟩⟩
  have h2 : v'.asIdeal ∈ (v.asIdeal.comap (algebraMap A₀ R)).primesOver R :=
    ⟨v'.isPrime, ⟨h⟩⟩
  obtain ⟨τ, hτ⟩ := hpre.exists_smul_eq ⟨v'.asIdeal, h2⟩ ⟨v.asIdeal, h1⟩
  refine ⟨τ, ?_⟩
  have hτ' : τ • v'.asIdeal = v.asIdeal := congrArg Subtype.val hτ
  rw [← hτ']
  ext r
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rw [show ((galRestrict A₀ K₀ L R) τ).toRingEquiv r = τ • r from rfl, inv_smul_smul]

open IsDedekindDomain in
open scoped nonZeroDivisors Pointwise in
private theorem count_spanSingleton_mul {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] (v : HeightOneSpectrum R) {x y : L} (hx : x ≠ 0)
    (hy : y ≠ 0) :
    FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ (x * y)) =
      FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ x) +
        FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ y) := by
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul]
  · rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  · rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]

open IsDedekindDomain in
open scoped nonZeroDivisors Pointwise in
private theorem count_spanSingleton_div {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] (v : HeightOneSpectrum R) {x y : L} (hx : x ≠ 0)
    (hy : y ≠ 0) :
    FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ (x / y)) =
      FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ x) -
        FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ y) := by
  have h := count_spanSingleton_mul (R := R) v (div_ne_zero hx hy) hy
  rw [div_mul_cancel₀ x hy] at h
  omega

open IsDedekindDomain in
open scoped nonZeroDivisors Pointwise in
private theorem count_spanSingleton_algebraMap_eq_count_factors {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ (algebraMap R L r)) =
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors := by
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe]
  simpa using hr

open IsDedekindDomain in
open scoped nonZeroDivisors Pointwise in
private theorem count_factors_span_eq_of_comap_ringEquiv {R : Type} [CommRing R] [IsDedekindDomain R] (e : R ≃+* R)
    (v v' : HeightOneSpectrum R) (hv : v'.asIdeal = Ideal.comap e v.asIdeal) {r : R} (hr : r ≠ 0) :
    (Associates.mk v'.asIdeal).count (Associates.mk (Ideal.span {r})).factors =
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {e r})).factors := by
  have h := _root_.GlobalTheory.QNorm.intValuation_of_eq_comap e v v' hv r
  rw [HeightOneSpectrum.intValuation_if_neg _ hr,
    HeightOneSpectrum.intValuation_if_neg _ (e.map_ne_zero_iff.mpr hr)] at h
  exact_mod_cast neg_injective (WithZero.exp_injective h)

open IsDedekindDomain in
open scoped nonZeroDivisors Pointwise in
private theorem count_galois_conj_spanSingleton {A₀ R K₀ L : Type} [CommRing A₀]
    [IsDedekindDomain A₀] [CommRing R] [IsDedekindDomain R] [Field K₀] [Field L]
    [Algebra A₀ K₀] [IsFractionRing A₀ K₀] [Algebra R L] [IsFractionRing R L] [Algebra A₀ R]
    [Algebra K₀ L] [Algebra A₀ L]
    [IsScalarTower A₀ R L] [IsScalarTower A₀ K₀ L] [IsIntegralClosure R A₀ L]
    [FiniteDimensional K₀ L] (σ : L ≃ₐ[K₀] L) (v v' : HeightOneSpectrum R)
    (hv : v'.asIdeal = Ideal.comap (galRestrict A₀ K₀ L R σ).toRingEquiv v.asIdeal) {x : L}
    (hx : x ≠ 0) :
    FractionalIdeal.count L v' (FractionalIdeal.spanSingleton R⁰ x) =
      FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ (σ x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hbL : algebraMap R L b ≠ 0 := (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)
  have haL : algebraMap R L a ≠ 0 := by
    intro h
    exact hx (by rw [h, zero_div])
  set g := (galRestrict A₀ K₀ L R σ).toRingEquiv
  have hga : g a ≠ 0 := g.map_ne_zero_iff.mpr ha0
  have hgb : g b ≠ 0 := g.map_ne_zero_iff.mpr hb0
  have hσa : σ (algebraMap R L a) = algebraMap R L (g a) := (algebraMap_galRestrict_apply A₀ σ a).symm
  have hσb : σ (algebraMap R L b) = algebraMap R L (g b) := (algebraMap_galRestrict_apply A₀ σ b).symm
  rw [map_div₀, hσa, hσb, count_spanSingleton_div v' haL hbL,
    count_spanSingleton_div v (by simpa using hga) (by simpa using hgb),
    count_spanSingleton_algebraMap_eq_count_factors v' ha0, count_spanSingleton_algebraMap_eq_count_factors v' hb0,
    count_spanSingleton_algebraMap_eq_count_factors v hga, count_spanSingleton_algebraMap_eq_count_factors v hgb,
    count_factors_span_eq_of_comap_ringEquiv g v v' hv ha0, count_factors_span_eq_of_comap_ringEquiv g v v' hv hb0]

open IsDedekindDomain in
open scoped nonZeroDivisors Pointwise in
private theorem count_spanSingleton_pow {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] (v : HeightOneSpectrum R) (x : L) (n : ℕ) :
    FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ (x ^ n)) =
      n * FractionalIdeal.count L v (FractionalIdeal.spanSingleton R⁰ x) := by
  rw [← FractionalIdeal.count_pow, FractionalIdeal.spanSingleton_pow]

open IsDedekindDomain in
open scoped nonZeroDivisors Pointwise in
private theorem count_algebraMap_of_unramified_lemma_6 {A₀ R K₀ L : Type} [CommRing A₀]
    [IsDedekindDomain A₀] [CommRing R] [IsDedekindDomain R] [Field K₀] [Field L]
    [Algebra A₀ K₀] [IsFractionRing A₀ K₀] [Algebra R L] [IsFractionRing R L] [Algebra A₀ R]
    [Algebra K₀ L] [Algebra A₀ L]
    [IsScalarTower A₀ R L] [IsScalarTower A₀ K₀ L] [IsIntegralClosure R A₀ L]
    [FiniteDimensional K₀ L] (Q : HeightOneSpectrum R) (P : HeightOneSpectrum A₀)
    (hP : P.asIdeal = Q.asIdeal.comap (algebraMap A₀ R))
    (hQ : ¬ Ideal.map (algebraMap A₀ R) (Q.asIdeal.comap (algebraMap A₀ R)) ≤ Q.asIdeal ^ 2)
    {f : A₀} (hf : f ≠ 0) :
    FractionalIdeal.count L Q (FractionalIdeal.spanSingleton R⁰ (algebraMap A₀ L f)) =
      FractionalIdeal.count K₀ P (FractionalIdeal.spanSingleton A₀⁰ (algebraMap A₀ K₀ f)) := by
  have hinj : Function.Injective (algebraMap A₀ R) := by
    intro a b hab
    apply IsFractionRing.injective A₀ K₀
    apply (algebraMap K₀ L).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A₀ R L, IsScalarTower.algebraMap_apply A₀ R L b, hab]
  have hfR : algebraMap A₀ R f ≠ 0 := by
    intro h
    exact hf (hinj (by rw [h, map_zero]))
  haveI : Q.asIdeal.LiesOver P.asIdeal := ⟨hP⟩
  haveI : FaithfulSMul A₀ R := (faithfulSMul_iff_algebraMap_injective A₀ R).mpr hinj
  have he : P.asIdeal.ramificationIdx' Q.asIdeal = 1 := by
    apply Ideal.ramificationIdx_spec
    · rw [pow_one, hP]
      exact Ideal.map_comap_le
    · rw [hP]
      exact hQ
  have hv := HeightOneSpectrum.intValuation_liesOver P Q f
  rw [he, pow_one, HeightOneSpectrum.intValuation_if_neg _ hf,
    HeightOneSpectrum.intValuation_if_neg _ hfR] at hv
  rw [IsScalarTower.algebraMap_apply A₀ R L, count_spanSingleton_algebraMap_eq_count_factors Q hfR,
    count_spanSingleton_algebraMap_eq_count_factors P hf]
  exact_mod_cast (neg_injective (WithZero.exp_injective hv)).symm

open IsDedekindDomain in
open scoped nonZeroDivisors Pointwise in

theorem _root_.GlobalTheory.DivisorDescent.descent_submodule : ∀ (A₀ R K₀ L : Type) [CommRing A₀]
    [IsDedekindDomain A₀] [CommRing R] [IsDedekindDomain R] [Field K₀] [Field L]
    [Algebra A₀ K₀] [IsFractionRing A₀ K₀] [Algebra R L] [IsFractionRing R L] [Algebra A₀ R]
    [Algebra K₀ L] [Algebra A₀ L]
    [IsScalarTower A₀ R L] [IsScalarTower A₀ K₀ L] [IsIntegralClosure R A₀ L]
    [FiniteDimensional K₀ L] [IsGalois K₀ L]
    (N : ℕ), 0 < N →
    (∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ →
      ¬ Ideal.map (algebraMap A₀ R) (Q.comap (algebraMap A₀ R)) ≤ Q ^ 2) →
    (∀ c : ClassGroup A₀, ∃ d, c = d ^ N) →
    ∀ w : L, w ≠ 0 → (∀ σ : L ≃ₐ[K₀] L, ∃ u : L, u ≠ 0 ∧ σ w = w * u ^ N) →
    ∃ (f : K₀) (J : Submodule R L), f ≠ 0 ∧ J ^ N = Submodule.span R {w / algebraMap K₀ L f} := by
  intro A₀ R K₀ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N hN hunr hCl w hw hconj
  classical
  have hinj : Function.Injective (algebraMap A₀ R) := by
    intro a b hab
    apply IsFractionRing.injective A₀ K₀
    apply (algebraMap K₀ L).injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A₀ R L, IsScalarTower.algebraMap_apply A₀ R L b, hab]
  haveI : FaithfulSMul A₀ R := (faithfulSMul_iff_algebraMap_injective A₀ R).mpr hinj
  haveI : Algebra.IsIntegral A₀ R := IsIntegralClosure.isIntegral_algebra A₀ L
  have hex : ∀ P : HeightOneSpectrum A₀, ∃ Q : HeightOneSpectrum R,
      P.asIdeal = Q.asIdeal.comap (algebraMap A₀ R) := by
    intro P
    obtain ⟨⟨Q, hQp, hQo⟩⟩ := Ideal.nonempty_primesOver (S := R) P.asIdeal
    refine ⟨⟨Q, hQp, ?_⟩, hQo.over⟩
    intro hQ
    apply P.ne_bot
    rw [hQo.over, hQ]
    exact Ideal.comap_bot_of_injective _ hinj
  choose Qof hQof using hex
  have hcong : ∀ Q Q' : HeightOneSpectrum R,
      Q.asIdeal.comap (algebraMap A₀ R) = Q'.asIdeal.comap (algebraMap A₀ R) →
      (N : ℤ) ∣ FractionalIdeal.count L Q' (FractionalIdeal.spanSingleton R⁰ w) -
        FractionalIdeal.count L Q (FractionalIdeal.spanSingleton R⁰ w) := by
    intro Q Q' h
    obtain ⟨σ, hσ⟩ := exists_galois_comap_eq_of_comap_eq (K₀ := K₀) (L := L) Q Q' h
    obtain ⟨u, hu, hσw⟩ := hconj σ
    rw [count_galois_conj_spanSingleton σ Q Q' hσ hw, hσw, count_spanSingleton_mul Q hw (pow_ne_zero _ hu),
      count_spanSingleton_pow]
    exact ⟨FractionalIdeal.count L Q (FractionalIdeal.spanSingleton R⁰ u), by ring⟩
  set r : HeightOneSpectrum A₀ → ℤ := fun P =>
    FractionalIdeal.count L (Qof P) (FractionalIdeal.spanSingleton R⁰ w) % N with hr
  have hr0 : ∀ P, 0 ≤ r P := fun P => Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  have hfinQ := Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors (K := L) (FractionalIdeal.spanSingleton R⁰ w))
  have hfinr : {P | r P ≠ 0}.Finite := by
    refine (hfinQ.preimage (f := Qof) ?_).subset ?_
    · intro P _ P' _ hPP'
      exact HeightOneSpectrum.ext (by rw [hQof P, hQof P', hPP'])
    · intro P hP h0
      apply hP
      simp only [hr, h0, Int.zero_emod]
  set aF : FractionalIdeal A₀⁰ K₀ :=
    ∏ᶠ P : HeightOneSpectrum A₀, (P.asIdeal : FractionalIdeal A₀⁰ K₀) ^ r P with haF
  have hcount_a : ∀ P, FractionalIdeal.count K₀ P aF = r P := fun P =>
    FractionalIdeal.count_finprod K₀ P r (Filter.eventually_cofinite.mpr (by simpa using hfinr))
  have hmul_fin : (Function.mulSupport fun P : HeightOneSpectrum A₀ =>
      P.asIdeal ^ (r P).toNat).Finite := by
    refine hfinr.subset ?_
    intro P hP h0
    apply hP
    simp [h0]
  set a : Ideal A₀ := ∏ᶠ P : HeightOneSpectrum A₀, P.asIdeal ^ (r P).toNat with ha
  have hacoe : (a : FractionalIdeal A₀⁰ K₀) = aF := by
    have hmap := MonoidHom.map_finprod (FractionalIdeal.coeIdealHom A₀⁰ K₀).toMonoidHom hmul_fin
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_pow,
      FractionalIdeal.coeIdealHom_apply] at hmap
    rw [ha, haF, hmap]
    refine finprod_congr fun P => ?_
    rw [← zpow_natCast, Int.toNat_of_nonneg (hr0 P)]
  have haF0 : aF ≠ 0 := by
    rw [haF]
    refine finprod_induction (fun I : FractionalIdeal A₀⁰ K₀ => I ≠ 0) one_ne_zero
      (fun _ _ hx hy => mul_ne_zero hx hy) fun P => zpow_ne_zero _ ?_
    exact FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot
  have ha0 : a ≠ ⊥ := by
    intro h
    apply haF0
    rw [← hacoe, h, FractionalIdeal.coeIdeal_bot]
  obtain ⟨b, x, y, hb, hx, hy, hxy⟩ :=
    _root_.GlobalTheory.DivisorDescent.exists_pow_class N hCl a ha0
  have hxyP : ∀ P : HeightOneSpectrum A₀,
      FractionalIdeal.count K₀ P (FractionalIdeal.spanSingleton A₀⁰ (algebraMap A₀ K₀ x)) + r P =
      FractionalIdeal.count K₀ P (FractionalIdeal.spanSingleton A₀⁰ (algebraMap A₀ K₀ y)) +
        N * FractionalIdeal.count K₀ P (b : FractionalIdeal A₀⁰ K₀) := by
    intro P
    have h := congrArg (fun I : Ideal A₀ => FractionalIdeal.count K₀ P (I : FractionalIdeal A₀⁰ K₀)) hxy
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow,
      FractionalIdeal.coeIdeal_span_singleton] at h
    rw [FractionalIdeal.count_mul, FractionalIdeal.count_mul, FractionalIdeal.count_pow, hacoe,
      hcount_a] at h
    · exact h
    all_goals first
      | exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hb)
      | (rw [hacoe]; exact haF0)
      | (rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
         exact (map_ne_zero_iff _ (IsFractionRing.injective A₀ K₀)).mpr (by assumption))
  have hxK : algebraMap A₀ K₀ x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A₀ K₀)).mpr hx
  have hyK : algebraMap A₀ K₀ y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A₀ K₀)).mpr hy
  have hxL : algebraMap A₀ L x ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A₀ K₀ L]
    exact (map_ne_zero _).mpr hxK
  have hyL : algebraMap A₀ L y ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A₀ K₀ L]
    exact (map_ne_zero _).mpr hyK
  have hwf : w / algebraMap K₀ L (algebraMap A₀ K₀ y / algebraMap A₀ K₀ x) =
      w * algebraMap A₀ L x / algebraMap A₀ L y := by
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    field_simp
  have hI0 : FractionalIdeal.spanSingleton R⁰ (w * algebraMap A₀ L x / algebraMap A₀ L y) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact div_ne_zero (mul_ne_zero hw hxL) hyL
  have hdvd : ∀ Q : HeightOneSpectrum R, (N : ℤ) ∣ FractionalIdeal.count L Q
      (FractionalIdeal.spanSingleton R⁰ (w * algebraMap A₀ L x / algebraMap A₀ L y)) := by
    intro Q
    have hP : (HeightOneSpectrum.under A₀ Q).asIdeal = Q.asIdeal.comap (algebraMap A₀ R) := rfl
    have hQ := hunr Q.asIdeal Q.isPrime Q.ne_bot
    rw [count_spanSingleton_div Q (mul_ne_zero hw hxL) hyL, count_spanSingleton_mul Q hw hxL,
      count_algebraMap_of_unramified_lemma_6 (K₀ := K₀) Q _ hP hQ hx, count_algebraMap_of_unramified_lemma_6 (K₀ := K₀) Q _ hP hQ hy]
    have h1 := hxyP (HeightOneSpectrum.under A₀ Q)
    obtain ⟨k, hk⟩ := hcong (Qof (HeightOneSpectrum.under A₀ Q)) Q
      (by rw [← hQof (HeightOneSpectrum.under A₀ Q), hP])
    have h3 := Int.mul_ediv_add_emod
      (FractionalIdeal.count L (Qof (HeightOneSpectrum.under A₀ Q)) (FractionalIdeal.spanSingleton R⁰ w)) N
    have h4 : r (HeightOneSpectrum.under A₀ Q) = FractionalIdeal.count L (Qof (HeightOneSpectrum.under A₀ Q))
        (FractionalIdeal.spanSingleton R⁰ w) % N := rfl
    exact ⟨k + FractionalIdeal.count L (Qof (HeightOneSpectrum.under A₀ Q))
        (FractionalIdeal.spanSingleton R⁰ w) / N +
        FractionalIdeal.count K₀ (HeightOneSpectrum.under A₀ Q) (b : FractionalIdeal A₀⁰ K₀), by
      linear_combination h1 + hk - h3 - h4⟩
  obtain ⟨J, hJ⟩ := _root_.GlobalTheory.DivisorDescent.exists_pow_eq_of_dvd_count N _ hI0 hdvd
  exact ⟨algebraMap A₀ K₀ y / algebraMap A₀ K₀ x, J, div_ne_zero hyK hxK, by
    rw [hwf, ← FractionalIdeal.coe_pow, hJ, FractionalIdeal.coe_spanSingleton]⟩

end GlobalTheory.DivisorDescent

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.NormCompat.NormCont

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_le'
  rw [← WithZero.exp_log hx] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]; omega

theorem exp_neg_one_pow (k : ℕ) : (WithZero.exp (-1 : ℤ)) ^ k = WithZero.exp (-(k : ℤ)) := by
  rw [← WithZero.exp_nsmul]; simp

theorem exists_exp_le_intValuation {R : Type} [CommRing R] [IsDedekindDomain R] {x : R} (hx : x ≠ 0) :
    ∃ k : ℕ, ∀ w : HeightOneSpectrum R, WithZero.exp (-(k : ℤ)) ≤ w.intValuation x := by
  classical
  have hI : Ideal.span {x} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  set F := (Ideal.finite_factors hI).toFinset
  refine ⟨F.sup fun w => (w.intValuation x).log.natAbs, fun w => ?_⟩
  by_cases hw : w ∈ F
  · have h0 := w.intValuation_ne_zero x hx
    have hle : (w.intValuation x).log.natAbs ≤ F.sup fun w => (w.intValuation x).log.natAbs :=
      Finset.le_sup (f := fun w => (w.intValuation x).log.natAbs) hw
    calc WithZero.exp (-((F.sup fun w => (w.intValuation x).log.natAbs : ℕ) : ℤ))
        ≤ WithZero.exp ((w.intValuation x).log) := by
          rw [WithZero.exp_le_exp]; omega
      _ = w.intValuation x := WithZero.exp_log h0
  · have h1 : w.intValuation x = 1 := by
      refine le_antisymm (w.intValuation_le_one x) (not_lt.1 fun h => hw ?_)
      rw [Set.Finite.mem_toFinset]
      exact (w.intValuation_lt_one_iff_dvd x).1 h
    rw [h1, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem pow_card_mul_prod_one_add {Ω : Type} [CommRing Ω] (A : Subring Ω) {ι : Type} [DecidableEq ι]
    (s : Finset ι) (a d : Ω) (ha : a ∈ A) (hd : d ∈ A) (x y : ι → Ω) (hy : ∀ i ∈ s, y i ∈ A)
    (hxy : ∀ i ∈ s, a * x i = d * y i) :
    ∃ β ∈ A, a ^ s.card * ∏ i ∈ s, (1 + x i) = a ^ s.card + d * β := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, A.zero_mem, by simp⟩
  | insert j s hj ih =>
    obtain ⟨β, hβ, h⟩ := ih (fun i hi => hy i (Finset.mem_insert_of_mem hi))
      (fun i hi => hxy i (Finset.mem_insert_of_mem hi))
    have hyj := hy j (Finset.mem_insert_self j s)
    refine ⟨y j * a ^ s.card + a * β + d * y j * β, ?_, ?_⟩
    · exact A.add_mem (A.add_mem (A.mul_mem hyj (A.pow_mem ha _)) (A.mul_mem ha hβ))
        (A.mul_mem (A.mul_mem hd hyj) hβ)
    · rw [Finset.card_insert_of_notMem hj, Finset.prod_insert hj, pow_succ]
      have e := hxy j (Finset.mem_insert_self j s)
      calc a ^ s.card * a * ((1 + x j) * ∏ i ∈ s, (1 + x i))
          = (a + a * x j) * (a ^ s.card * ∏ i ∈ s, (1 + x i)) := by ring
        _ = (a + d * y j) * (a ^ s.card + d * β) := by rw [e, h]
        _ = _ := by ring

end GlobalTheory.NormCompat.NormCont

namespace GlobalTheory.NormCompat.NormCont

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem exists_mem_comap_not_mem (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K))
    (hw : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) :
    ∃ e : 𝓞 E, algebraMap (𝓞 E) (𝓞 K) e ∈ w.asIdeal ∧ e ∉ v.asIdeal := by
  by_contra h
  push_neg at h
  have hmax : (w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K))).IsMaximal :=
    haveI := w.isMaximal; Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w.asIdeal
  exact hw (hmax.eq_of_le v.isPrime.ne_top fun e he => h e he)

theorem exists_mul_mem_integers (v : HeightOneSpectrum (𝓞 E)) (y : K)
    (hy : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      w.valuation K y ≤ 1) :
    ∃ a : 𝓞 E, a ∉ v.asIdeal ∧ algebraMap E K (a : E) * y ∈ (algebraMap (𝓞 K) K).range := by
  classical
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  obtain ⟨k, hk⟩ := exists_exp_le_intValuation hc0
  have hI : Ideal.span {c} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hc0
  set F := (Ideal.finite_factors hI).toFinset
  let f : HeightOneSpectrum (𝓞 K) → 𝓞 E := fun w =>
    if h : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal then
      Classical.choose (exists_mem_comap_not_mem v w h) else 1
  have hf : ∀ w, f w ∉ v.asIdeal := fun w => by
    by_cases h : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal
    · simp only [f, dif_pos h]; exact (Classical.choose_spec (exists_mem_comap_not_mem v w h)).2
    · simp only [f, dif_neg h]; exact fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hfw : ∀ w, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal →
      algebraMap (𝓞 E) (𝓞 K) (f w) ∈ w.asIdeal := fun w h => by
    simp only [f, dif_pos h]; exact (Classical.choose_spec (exists_mem_comap_not_mem v w h)).1
  let a : 𝓞 E := ∏ w ∈ F, f w ^ k
  have ha : a ∉ v.asIdeal := by
    refine Finset.prod_induction _ (· ∉ v.asIdeal) (fun x y hx hy h => (v.isPrime.mem_or_mem h).elim hx hy)
      (fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)) fun w _ h => hf w (v.isPrime.mem_of_pow_mem k h)
  refine ⟨a, ha, HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K _ fun w => ?_⟩
  have hA : algebraMap E K (a : E) = ((algebraMap (𝓞 E) (𝓞 K) a : 𝓞 K) : K) := rfl
  have hc' : w.valuation K (c : K) ≠ 0 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact w.intValuation_ne_zero c hc0
  rw [hA, map_mul, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap]
  rw [HeightOneSpectrum.valuation_of_algebraMap] at hc'
  have hb1 := w.intValuation_le_one b
  have ha1 := w.intValuation_le_one (algebraMap (𝓞 E) (𝓞 K) a)
  by_cases hv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal
  · have := hy w hv
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap] at this
    calc w.intValuation (algebraMap (𝓞 E) (𝓞 K) a) * (w.intValuation b / w.intValuation c)
        ≤ 1 * (w.intValuation b / w.intValuation c) := mul_le_mul' ha1 le_rfl
      _ ≤ 1 := by rw [one_mul]; exact this
  by_cases hwF : w ∈ F
  · have hlt : w.intValuation (algebraMap (𝓞 E) (𝓞 K) (f w)) < 1 :=
      (w.intValuation_lt_one_iff_mem _).2 (hfw w hv)
    have hle : w.intValuation (algebraMap (𝓞 E) (𝓞 K) a) ≤ WithZero.exp (-(k : ℤ)) := by
      have e : a = f w ^ k * ∏ x ∈ F.erase w, f x ^ k := (Finset.mul_prod_erase F (fun x => f x ^ k) hwF).symm
      rw [e, map_mul, map_mul, map_pow, map_pow, ← exp_neg_one_pow]
      calc w.intValuation (algebraMap (𝓞 E) (𝓞 K) (f w)) ^ k *
            w.intValuation (algebraMap (𝓞 E) (𝓞 K) (∏ x ∈ F.erase w, f x ^ k))
          ≤ w.intValuation (algebraMap (𝓞 E) (𝓞 K) (f w)) ^ k * 1 := mul_le_mul' le_rfl (w.intValuation_le_one _)
        _ ≤ WithZero.exp (-1) ^ k := by rw [mul_one]; exact pow_le_pow_left' (le_exp_neg_one_of_lt_one hlt) k
    rw [mul_div_assoc', div_le_one₀ (zero_lt_iff.2 hc')]
    calc w.intValuation (algebraMap (𝓞 E) (𝓞 K) a) * w.intValuation b
        ≤ WithZero.exp (-(k : ℤ)) * 1 := mul_le_mul' hle hb1
      _ ≤ w.intValuation c := by rw [mul_one]; exact hk w
  · have h1 : w.intValuation c = 1 := by
      refine le_antisymm (w.intValuation_le_one c) (not_lt.1 fun h => hwF ?_)
      rw [Set.Finite.mem_toFinset]
      exact (w.intValuation_lt_one_iff_dvd c).1 h
    rw [h1, div_one]
    calc w.intValuation (algebraMap (𝓞 E) (𝓞 K) a) * w.intValuation b ≤ 1 * 1 := mul_le_mul' ha1 hb1
      _ = 1 := one_mul 1

end GlobalTheory.NormCompat.NormCont

namespace GlobalTheory.NormCompat.NormCont

theorem norm_close_to_one : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) (M : ℕ), ∃ M' : ℕ, ∀ z : K,
    (∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      w.valuation K (z - 1) ≤ WithZero.exp (-(M' : ℤ))) →
    v.valuation E (Algebra.norm E z - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  intro E K _ _ _ _ _ v M
  classical
  obtain ⟨π, hπv, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hπK : algebraMap (𝓞 E) (𝓞 K) π ≠ 0 := by
    intro h
    apply hπ0
    have h2 : ((algebraMap (𝓞 E) (𝓞 K) π : 𝓞 K) : K) = 0 := by rw [h]; rfl
    have h3 : algebraMap E K (π : E) = 0 := h2
    rw [map_eq_zero] at h3
    exact_mod_cast h3
  obtain ⟨k, hk⟩ := exists_exp_le_intValuation hπK
  refine ⟨k * M, fun z hz => ?_⟩
  set d : 𝓞 E := π ^ M with hd
  have hdE : (d : E) ≠ 0 := by
    rw [hd]; push_cast; exact pow_ne_zero _ (by exact_mod_cast hπ0)
  have hdK : algebraMap E K (d : E) ≠ 0 := (map_ne_zero _).2 hdE
  have hdw : ∀ w : HeightOneSpectrum (𝓞 K), WithZero.exp (-((k * M : ℕ) : ℤ)) ≤ w.valuation K (algebraMap E K (d : E)) := by
    intro w
    have e : algebraMap E K (d : E) = ((algebraMap (𝓞 E) (𝓞 K) d : 𝓞 K) : K) := rfl
    rw [e, HeightOneSpectrum.valuation_of_algebraMap, hd, map_pow, map_pow]
    calc WithZero.exp (-((k * M : ℕ) : ℤ)) = WithZero.exp (-(k : ℤ)) ^ M := by
          rw [← WithZero.exp_nsmul]; congr 1; push_cast; ring
      _ ≤ _ := pow_le_pow_left' (hk w) M
  obtain ⟨a, ha, r, hr⟩ := exists_mul_mem_integers v ((z - 1) / algebraMap E K (d : E)) fun w hw => by
    have h0 : w.valuation K (algebraMap E K (d : E)) ≠ 0 := by
      rw [Ne, map_eq_zero]; exact hdK
    rw [map_div₀, div_le_one₀ (zero_lt_iff.2 h0)]
    exact (hz w hw).trans (hdw w)

  have hadr : algebraMap E K (a : E) * (z - 1) = algebraMap E K (d : E) * (r : K) := by
    change _ = _ * algebraMap (𝓞 K) K r
    rw [hr]; field_simp
  let Ω := AlgebraicClosure E
  have hN := Algebra.norm_eq_prod_embeddings E Ω z
  let A : Subring Ω := (integralClosure ℤ Ω).toSubring
  have hintE : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x =>
    (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E Ω)
  obtain ⟨β, hβ, hprod⟩ := pow_card_mul_prod_one_add A Finset.univ (algebraMap E Ω (a : E)) (algebraMap E Ω (d : E))
    (hintE a) (hintE d) (fun σ : K →ₐ[E] Ω => σ (z - 1)) (fun σ => σ (r : K))
    (fun σ _ => (RingOfIntegers.isIntegral_coe r).map σ.toRingHom.toIntAlgHom)
    (fun σ _ => by
      have := congrArg σ hadr
      simpa only [map_mul, AlgHom.commutes] using this)
  set n := (Finset.univ : Finset (K →ₐ[E] Ω)).card
  have hprod' : algebraMap E Ω ((a : E) ^ n * Algebra.norm E z) = algebraMap E Ω ((a : E) ^ n) + algebraMap E Ω (d : E) * β := by
    rw [map_mul, hN, map_pow, ← hprod]
    congr 1
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [map_sub, map_one]; ring
  obtain ⟨e, he_def⟩ : ∃ e : E, e = (a : E) ^ n * (Algebra.norm E z - 1) / d := ⟨_, rfl⟩
  have hde : (d : E) * e = (a : E) ^ n * (Algebra.norm E z - 1) := by
    rw [he_def]; field_simp
  have he : algebraMap E Ω e = β := by
    have hd' : algebraMap E Ω (d : E) ≠ 0 := (map_ne_zero _).2 hdE
    refine mul_left_cancel₀ hd' ?_
    rw [← map_mul, hde, mul_sub, mul_one, map_sub, hprod']; ring
  have heI : IsIntegral ℤ e := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E Ω) (algebraMap E Ω).injective]
    show IsIntegral ℤ (algebraMap E Ω e)
    rw [he]; exact hβ
  have hev : v.valuation E e ≤ 1 := by
    obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, (x : E) = e := ⟨⟨e, heI⟩, rfl⟩
    rw [← hx]; exact v.valuation_le_one _
  have hav : v.valuation E (a : E) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (v.intValuation_le_one a) (not_lt.1 fun h => ha ((v.intValuation_lt_one_iff_mem a).1 h))
  have hdv : v.valuation E (d : E) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [hd]; push_cast
    rw [map_pow, ← exp_neg_one_pow]
    exact pow_le_pow_left' (le_exp_neg_one_of_lt_one ((v.valuation_lt_one_iff_mem π).2 hπv)) M
  have hN1 : Algebra.norm E z - 1 = e * d / (a : E) ^ n := by
    have ha0 : (a : E) ≠ 0 := by
      intro h0; apply ha
      have : a = 0 := by exact_mod_cast h0
      rw [this]; exact zero_mem _
    rw [he_def]; field_simp
  rw [hN1, map_div₀, map_mul, map_pow, hav, one_pow, div_one]
  calc v.valuation E e * v.valuation E (d : E) ≤ 1 * WithZero.exp (-(M : ℤ)) := mul_le_mul' hev hdv
    _ = _ := one_mul _

end GlobalTheory.NormCompat.NormCont

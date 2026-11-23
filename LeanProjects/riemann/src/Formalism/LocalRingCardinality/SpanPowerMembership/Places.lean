import Formalism.LocalRingCardinality.DataRows
import Formalism.LocalRingCardinality.DataArith

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.BasicNotions.Examples₂

namespace PlacesToy

variable {K : Type} [Field K] [NumberField K]

theorem valuation_ne_zero' (w : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    w.valuation K x ≠ 0 := by
  simpa using hx

theorem vAdd_mul (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul (valuation_ne_zero' w hx) (valuation_ne_zero' w hy)]
  ring

theorem vAdd_one (w : HeightOneSpectrum (𝓞 K)) : vAdd w (1 : K) = 0 := by
  simp [vAdd]

theorem vAdd_add (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (vAdd w x) (vAdd w y) ≤ vAdd w (x + y) := by
  unfold vAdd
  have h := (w.valuation K).map_add x y
  rcases le_total (w.valuation K x) (w.valuation K y) with h' | h'
  · have h2 : w.valuation K (x + y) ≤ w.valuation K y := h.trans (max_le h' le_rfl)
    have := (WithZero.log_le_log (valuation_ne_zero' w hxy) (valuation_ne_zero' w hy)).2 h2
    exact (min_le_right _ _).trans (by omega)
  · have h2 : w.valuation K (x + y) ≤ w.valuation K x := h.trans (max_le le_rfl h')
    have := (WithZero.log_le_log (valuation_ne_zero' w hxy) (valuation_ne_zero' w hx)).2 h2
    exact (min_le_left _ _).trans (by omega)

open Classical in

def valFun (w : HeightOneSpectrum (𝓞 K)) (x : K) : WithTop ℤ :=
  if x = 0 then ⊤ else ((vAdd w x : ℤ) : WithTop ℤ)

theorem valFun_of_ne (w : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    valFun w x = ((vAdd w x : ℤ) : WithTop ℤ) := by
  simp [valFun, hx]

def valW (w : HeightOneSpectrum (𝓞 K)) : AddValuation K (WithTop ℤ) :=
  AddValuation.of (valFun w) (by simp [valFun]) (by simp [valFun, vAdd_one])
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; rw [zero_add]; exact min_le_right _ _
      by_cases hy : y = 0
      · subst hy; rw [add_zero]; exact min_le_left _ _
      by_cases hxy : x + y = 0
      · rw [show valFun w (x + y) = ⊤ from by simp [valFun, hxy]]; exact le_top
      rw [valFun_of_ne w hx, valFun_of_ne w hy, valFun_of_ne w hxy, ← WithTop.coe_min,
        WithTop.coe_le_coe]
      exact vAdd_add w hx hy hxy)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp [valFun]
      by_cases hy : y = 0
      · subst hy; simp [valFun]
      rw [valFun_of_ne w hx, valFun_of_ne w hy, valFun_of_ne w (mul_ne_zero hx hy),
        vAdd_mul w hx hy]
      rfl)

theorem valW_of_ne (w : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    valW w x = ((vAdd w x : ℤ) : WithTop ℤ) := by
  simp [valW, valFun_of_ne w hx]

theorem valW_zero (w : HeightOneSpectrum (𝓞 K)) : valW w (0 : K) = ⊤ := by
  simp [valW]

theorem valW_surj (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    ∃ x : K, valW w x = ((n : ℤ) : WithTop ℤ) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact WithZero.zero_ne_coe hπ
  refine ⟨π ^ n, ?_⟩
  rw [valW_of_ne w (zpow_ne_zero _ hπ0)]
  congr 1
  unfold vAdd
  rw [map_zpow₀, hπ, WithZero.log_zpow, WithZero.log_exp]
  simp

end PlacesToy

namespace PlacesToy

variable {K : Type} [Field K] [NumberField K]

theorem exists_prime_mem (w : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ((p : 𝓞 K) ∈ w.asIdeal) := by
  have key : ∀ n : ℕ, 2 ≤ n → ((n : 𝓞 K) ∈ w.asIdeal) →
      ∃ p : ℕ, p.Prime ∧ ((p : 𝓞 K) ∈ w.asIdeal) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hmem
      by_cases hp : n.Prime
      · exact ⟨n, hp, hmem⟩
      · have hlt : n.minFac < n := (Nat.not_prime_iff_minFac_lt hn).1 hp
        have hmp : n.minFac.Prime := Nat.minFac_prime (by omega)
        have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
        have hsplit : (n : 𝓞 K) = (n.minFac : 𝓞 K) * ((n / n.minFac : ℕ) : 𝓞 K) := by
          rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
        rw [hsplit] at hmem
        rcases w.isPrime.mem_or_mem hmem with h | h
        · exact ⟨_, hmp, h⟩
        · have h2 : 2 ≤ n.minFac := hmp.two_le
          have hq0 : n / n.minFac ≠ 0 := by
            intro h0
            rw [Nat.div_eq_zero_iff] at h0
            omega
          have hq1 : n / n.minFac ≠ 1 := by
            intro h1
            apply hp
            have : n = n.minFac := by
              have := Nat.div_mul_cancel hdvd
              rw [h1, one_mul] at this
              exact this.symm
            rw [this]; exact hmp
          exact ih (n / n.minFac) (Nat.div_lt_self (by omega) h2) ((Nat.two_le_iff _).2 ⟨hq0, hq1⟩) h
  refine key (Ideal.absNorm w.asIdeal) ?_ (Ideal.absNorm_mem w.asIdeal)
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
  omega

open Classical in

def resCharW (w : HeightOneSpectrum (𝓞 K)) : ℕ := Nat.find (exists_prime_mem w)

theorem resCharW_prime (w : HeightOneSpectrum (𝓞 K)) : (resCharW w).Prime := by
  classical
  exact (Nat.find_spec (exists_prime_mem w)).1

theorem resCharW_mem (w : HeightOneSpectrum (𝓞 K)) : ((resCharW w : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  classical
  exact (Nat.find_spec (exists_prime_mem w)).2

omit [NumberField K] in
theorem prime_mem_unique (w : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpw : (p : 𝓞 K) ∈ w.asIdeal) (hqw : (q : 𝓞 K) ∈ w.asIdeal) : p = q := by
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have h1 : ((a : 𝓞 K) * (p : 𝓞 K) + (b : 𝓞 K) * (q : 𝓞 K)) ∈ w.asIdeal :=
    w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hpw) (w.asIdeal.mul_mem_left _ hqw)
  have h2 : ((a : 𝓞 K) * (p : 𝓞 K) + (b : 𝓞 K) * (q : 𝓞 K)) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 K) hab
    push_cast at this
    exact this
  rw [h2] at h1
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem under_eq_span (w : HeightOneSpectrum (𝓞 K)) :
    Ideal.span {((resCharW w : ℕ) : ℤ)} = w.asIdeal.under ℤ := by
  have hp := resCharW_prime w
  have hmax : (Ideal.span {((resCharW w : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  refine hmax.eq_of_le ?_ ?_
  · exact Ideal.comap_ne_top _ w.isPrime.ne_top
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ((resCharW w : ℕ) : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) w.asIdeal
    rw [Ideal.mem_comap]
    simpa using resCharW_mem w

instance liesOver_resCharW (w : HeightOneSpectrum (𝓞 K)) :
    w.asIdeal.LiesOver (Ideal.span {((resCharW w : ℕ) : ℤ)}) :=
  ⟨under_eq_span w⟩

theorem eWL_pos (w : HeightOneSpectrum (𝓞 K)) : 0 < eWL K w := by
  have := w.isPrime
  exact Ideal.ramificationIdx_pos w.asIdeal ℤ

theorem vAdd_resCharW (w : HeightOneSpectrum (𝓞 K)) :
    vAdd w (((resCharW w : ℕ) : K)) = (eWL K w : ℤ) := by
  have := w.isPrime
  set p := resCharW w with hpdef
  have hp := resCharW_prime w
  have hr : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hmap : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((p : ℕ) : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hne : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact hr
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {((p : ℕ) : ℤ)})
    w.asIdeal hne
  rw [hmap] at he
  unfold vAdd eWL
  rw [he, show ((p : ℕ) : K) = algebraMap (𝓞 K) K ((p : ℕ) : 𝓞 K) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap, w.intValuation_eq_exp_neg_multiplicity hr,
    WithZero.log_exp, neg_neg]

theorem valW_resCharW (w : HeightOneSpectrum (𝓞 K)) :
    valW w (((resCharW w : ℕ) : K)) = (((eWL K w : ℕ) : ℤ) : WithTop ℤ) := by
  have hp := resCharW_prime w
  rw [valW_of_ne w (Nat.cast_ne_zero.2 hp.ne_zero), vAdd_resCharW]

end PlacesToy

namespace PlacesToy

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def starO : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv (starRingAut (R := K) : K ≃+* K)

omit [NumberField K] in
@[simp] theorem starO_coe (x : 𝓞 K) : ((starO x : 𝓞 K) : K) = star (x : K) := rfl

omit [NumberField K] in
@[simp] theorem starO_starO (x : 𝓞 K) : starO (starO x) = x := by
  apply RingOfIntegers.ext
  rw [starO_coe, starO_coe, star_star]

omit [NumberField K] in
theorem starO_symm (x : 𝓞 K) : (starO (K := K)).symm x = starO x := by
  apply (starO (K := K)).injective
  rw [RingEquiv.apply_symm_apply, starO_starO]

def conjW (w : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.equivOfRingEquiv (starO (K := K)) w

omit [NumberField K] in
theorem conjW_asIdeal (w : HeightOneSpectrum (𝓞 K)) :
    (conjW w).asIdeal = w.asIdeal.comap ((starO (K := K)).symm : 𝓞 K →+* 𝓞 K) := rfl

omit [NumberField K] in
theorem conjW_asIdeal' (w : HeightOneSpectrum (𝓞 K)) :
    (conjW w).asIdeal = w.asIdeal.map (starO (K := K)) := by
  ext x
  rw [← Ideal.symm_apply_mem_of_equiv_iff]
  rfl

omit [NumberField K] in
theorem mem_conjW_pow (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (n : ℕ) :
    r ∈ (conjW w).asIdeal ^ n ↔ starO r ∈ w.asIdeal ^ n := by
  rw [conjW_asIdeal', ← Ideal.map_pow, ← Ideal.symm_apply_mem_of_equiv_iff, starO_symm]

omit [NumberField K] in
theorem conjW_conjW (w : HeightOneSpectrum (𝓞 K)) : conjW (conjW w) = w := by
  ext x
  change x ∈ Ideal.comap _ (Ideal.comap _ w.asIdeal) ↔ x ∈ w.asIdeal
  simp only [Ideal.mem_comap, RingHom.coe_coe, starO_symm, starO_starO]

theorem intValuation_conjW (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    (conjW w).intValuation r = w.intValuation (starO r) := by
  by_cases hr : r = 0
  · subst hr; simp
  have hr' : starO r ≠ 0 := by
    intro h; apply hr; rw [← starO_starO r, h, map_zero]
  rw [(conjW w).intValuation_eq_exp_neg_multiplicity hr, w.intValuation_eq_exp_neg_multiplicity hr']
  set k := multiplicity (conjW w).asIdeal (Ideal.span {r})
  set k' := multiplicity w.asIdeal (Ideal.span {starO r})
  have h : ∀ n : ℕ, n ≤ k ↔ n ≤ k' := by
    intro n
    have h1 := (conjW w).intValuation_le_pow_iff_mem r n
    have h2 := w.intValuation_le_pow_iff_mem (starO r) n
    rw [(conjW w).intValuation_eq_exp_neg_multiplicity hr, WithZero.exp_le_exp] at h1
    rw [w.intValuation_eq_exp_neg_multiplicity hr', WithZero.exp_le_exp] at h2
    rw [mem_conjW_pow] at h1
    have e1 : n ≤ k ↔ -(k : ℤ) ≤ -(n : ℤ) := by omega
    have e2 : n ≤ k' ↔ -(k' : ℤ) ≤ -(n : ℤ) := by omega
    rw [e1, e2, h1, h2]
  have hk : k = k' := le_antisymm ((h k).1 le_rfl) ((h k').2 le_rfl)
  rw [hk]

theorem valuation_conjW (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    (conjW w).valuation K x = w.valuation K (star x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hs : star (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) =
      algebraMap (𝓞 K) K (starO a) / algebraMap (𝓞 K) K (starO b) := by
    rw [star_div₀]
    rfl
  rw [hs, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_conjW, intValuation_conjW]

theorem vAdd_conjW (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    vAdd (conjW w) x = vAdd w (star x) := by
  unfold vAdd
  rw [valuation_conjW]

theorem valW_conjW (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    valW (conjW w) x = valW w (star x) := by
  by_cases hx : x = 0
  · subst hx; rw [star_zero, valW_zero, valW_zero]
  have hx' : star x ≠ 0 := by rwa [Ne, star_eq_zero]
  rw [valW_of_ne _ hx, valW_of_ne _ hx', vAdd_conjW]

def placesOf (K : Type) [Field K] [NumberField K] [StarRing K] : Formalism.BasicNotions.Rows.Places K where
  Pl := HeightOneSpectrum (𝓞 K)
  val := valW
  conj := conjW
  conj_conj := conjW_conjW
  resChar := resCharW
  resChar_prime := resCharW_prime
  ramIdx := eWL K
  ramIdx_pos := eWL_pos
  val_surj := valW_surj
  val_resChar := valW_resCharW

end PlacesToy

abbrev placesOf (K : Type) [Field K] [NumberField K] [StarRing K] : Formalism.BasicNotions.Rows.Places K :=
  PlacesToy.placesOf K

section Coherence

variable (K : Type) [Field K] [NumberField K] [StarRing K]

theorem placesOf_val_eq (w : (placesOf K).Pl) (x : K) (hx : x ≠ 0) :
    (placesOf K).val w x = ((vAdd ((Equiv.refl _ : (placesOf K).Pl ≃ HeightOneSpectrum (𝓞 K)) w) x : ℤ) :
      WithTop ℤ) :=
  PlacesToy.valW_of_ne w hx

theorem placesOf_ram_eq (w : (placesOf K).Pl) :
    (placesOf K).ramIdx w = eWL K ((Equiv.refl _ : (placesOf K).Pl ≃ HeightOneSpectrum (𝓞 K)) w) :=
  rfl

theorem placesOf_conj_val (w : (placesOf K).Pl) (x : K) :
    (placesOf K).val ((placesOf K).conj w) x = (placesOf K).val w (star x) :=
  PlacesToy.valW_conjW w x

end Coherence

theorem bridge_unit_rule_holds : Formalism.BasicNotions.bridge_unit_rule := by
  intro K _ _ l w hl hlw
  obtain rfl := PlacesToy.prime_mem_unique w hl (PlacesToy.resCharW_prime w) hlw
    (PlacesToy.resCharW_mem w)
  exact PlacesToy.vAdd_resCharW w

end Formalism.BasicNotions.Examples₂

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeMapPrimeMap
open NumberField IsDedekindDomain GlobalTheory.FixNormCls
open scoped Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.LocalDivisor

variable {E : Type} [Field E] [NumberField E]

theorem ord_neg (P : HeightOneSpectrum (𝓞 E)) (x : E) : ord P (-x) = ord P x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h1 : ord P (-1 : E) = 0 := by
    have := ord_mul P (x := (-1 : E)) (y := -1) (by norm_num) (by norm_num)
    rw [show (-1 : E) * -1 = 1 by ring, ord_one] at this
    linarith
  rw [show -x = (-1 : E) * x by ring, ord_mul P (by norm_num) hx, h1, zero_add]

theorem ord_nonneg_of_isIntegral (P : HeightOneSpectrum (𝓞 E)) {y : E} (hy : IsIntegral ℤ y) :
    0 ≤ ord P y := by
  unfold ord
  have : y = algebraMap (𝓞 E) E (IsIntegralClosure.mk' (𝓞 E) y hy) :=
    (IsIntegralClosure.algebraMap_mk' (𝓞 E) y hy).symm
  rw [this, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg _ _ _

theorem ord_algebraMap_eq_zero (P : HeightOneSpectrum (𝓞 E)) {r : 𝓞 E} (hr : r ∉ P.asIdeal) :
    ord P (algebraMap (𝓞 E) E r) = 0 := by
  have hr0 : r ≠ 0 := by rintro rfl; exact hr P.asIdeal.zero_mem
  unfold ord
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe E P (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])]
  have hne : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [Nat.cast_eq_zero]
  by_contra hc
  exact hr (Ideal.dvd_span_singleton.1 ((Associates.count_ne_zero_iff_dvd hne P.irreducible).1 hc))

theorem natCast_not_mem (P : HeightOneSpectrum (𝓞 E)) {ℓ d : ℕ} (hℓ : ℓ.Prime)
    (hP : (ℓ : 𝓞 E) ∈ P.asIdeal) (hd : ¬ ℓ ∣ d) : (d : 𝓞 E) ∉ P.asIdeal := by
  intro h
  have hc : IsCoprime (ℓ : ℤ) (d : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hd)
  obtain ⟨u, v, huv⟩ := hc
  have : (1 : 𝓞 E) ∈ P.asIdeal := by
    have e : (((u * ℓ + v * d : ℤ)) : 𝓞 E) = 1 := by rw [huv]; simp
    rw [← e]; push_cast
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hP) (P.asIdeal.mul_mem_left _ h)
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem ord_natCast_coprime (P : HeightOneSpectrum (𝓞 E)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hP : (ℓ : 𝓞 E) ∈ P.asIdeal) {d : ℕ} (hd : ¬ ℓ ∣ d) : ord P (d : E) = 0 := by
  rw [← map_natCast (algebraMap (𝓞 E) E) d]
  exact ord_algebraMap_eq_zero P (natCast_not_mem P hℓ hP hd)

theorem exists_prime_mem (P : HeightOneSpectrum (𝓞 E)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 E) ∈ P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  suffices ∀ n : ℕ, n ≠ 0 → (n : 𝓞 E) ∈ P.asIdeal → ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 E) ∈ P.asIdeal from
    this _ h0 (Ideal.absNorm_mem P.asIdeal)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    have hn1 : n ≠ 1 := by
      rintro rfl
      simp only [Nat.cast_one] at hmem
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hmem)
    have hp := Nat.minFac_prime hn1
    have e : n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm
    have hm0 : n / n.minFac ≠ 0 := by
      intro h; rw [h, mul_zero] at e; exact hn e
    rw [e] at hmem
    push_cast at hmem
    rcases P.isPrime.mem_or_mem hmem with h | h
    · exact ⟨_, hp, h⟩
    · refine ih _ ?_ hm0 h
      have := hp.two_le
      have : 0 < n / n.minFac := Nat.pos_of_ne_zero hm0
      conv_rhs => rw [e]
      nlinarith

theorem prime_eq_of_mem (P : HeightOneSpectrum (𝓞 E)) {ℓ ℓ' : ℕ} (h : ℓ.Prime) (h' : ℓ'.Prime)
    (hm : (ℓ : 𝓞 E) ∈ P.asIdeal) (hm' : (ℓ' : 𝓞 E) ∈ P.asIdeal) : ℓ = ℓ' := by
  by_contra hne
  exact natCast_not_mem P h hm (by rwa [Nat.prime_dvd_prime_iff_eq h h']) hm'

theorem ord_pow (P : HeightOneSpectrum (𝓞 E)) {x : E} (hx : x ≠ 0) (n : ℕ) :
    ord P (x ^ n) = n * ord P x := by
  induction n with
  | zero => simp [ord_one]
  | succ n ih => rw [pow_succ, ord_mul P (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem ord_zpow (P : HeightOneSpectrum (𝓞 E)) {x : E} (hx : x ≠ 0) (n : ℤ) :
    ord P (x ^ n) = n * ord P x := by
  cases n with
  | ofNat n => simp only [Int.ofNat_eq_coe, zpow_natCast]; exact ord_pow P hx n
  | negSucc n => rw [zpow_negSucc, ord_inv, ord_pow P hx, Int.negSucc_eq]; push_cast; ring

theorem ord_prod (P : HeightOneSpectrum (𝓞 E)) {ι : Type} (s : Finset ι) (g : ι → E)
    (hg : ∀ i ∈ s, g i ≠ 0) : ord P (∏ i ∈ s, g i) = ∑ i ∈ s, ord P (g i) := by
  induction s using Finset.induction_on with
  | empty => simp [ord_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul P (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

theorem ord_natCast (P : HeightOneSpectrum (𝓞 E)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hP : (ℓ : 𝓞 E) ∈ P.asIdeal) {n : ℕ} (hn : n ≠ 0) :
    ord P (n : E) = padicValNat ℓ n * ord P (ℓ : E) := by
  haveI := Fact.mk hℓ
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := ℓ) (n := n)
  have hmd : ¬ ℓ ∣ m := fun h =>
    (pow_succ_padicValNat_not_dvd (p := ℓ) hn) (by conv_rhs => rw [hm]
                                                   rw [pow_succ]; exact mul_dvd_mul_left _ h)
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact hn hm
  have hl0 : (ℓ : E) ≠ 0 := Nat.cast_ne_zero.2 hℓ.ne_zero
  conv_lhs => rw [hm, Nat.cast_mul, Nat.cast_pow]
  rw [ord_mul P (pow_ne_zero _ hl0) (Nat.cast_ne_zero.2 hm0), ord_pow P hl0,
    ord_natCast_coprime P hℓ hP hmd, add_zero]

theorem ord_intCast (P : HeightOneSpectrum (𝓞 E)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hP : (ℓ : 𝓞 E) ∈ P.asIdeal) {z : ℤ} (hz : z ≠ 0) :
    ord P (z : E) = padicValInt ℓ z * ord P (ℓ : E) := by
  have h := ord_natCast P hℓ hP (Int.natAbs_ne_zero.2 hz)
  have hv : padicValInt ℓ z = padicValNat ℓ z.natAbs := rfl
  rw [hv, ← h]
  rcases Int.natAbs_eq z with e | e
  · conv_lhs => rw [e]
    simp
  · conv_lhs => rw [e]
    rw [Int.cast_neg, ord_neg]
    simp

theorem ord_ratCast (P : HeightOneSpectrum (𝓞 E)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hP : (ℓ : 𝓞 E) ∈ P.asIdeal) {q : ℚ} (hq : q ≠ 0) :
    ord P (q : E) = padicValRat ℓ q * ord P (ℓ : E) := by
  rw [Rat.cast_def, ord_div P (Int.cast_ne_zero.2 (Rat.num_ne_zero.2 hq))
    (Nat.cast_ne_zero.2 q.den_pos.ne'), ord_intCast P hℓ hP (Rat.num_ne_zero.2 hq),
    ord_natCast P hℓ hP q.den_pos.ne']
  simp only [padicValRat]
  ring

theorem ord_finite (x : E) : {P : HeightOneSpectrum (𝓞 E) | ord P x ≠ 0}.Finite := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ord_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hab : a * b ≠ 0 := mul_ne_zero ha0 hb0
  refine (Ideal.finite_factors (I := Ideal.span {a * b}) (by simpa using hab)).subset fun P hP => ?_
  simp only [Set.mem_setOf_eq] at hP ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hn
  apply hP
  have haP : a ∉ P.asIdeal := fun h => hn (P.asIdeal.mul_mem_right _ h)
  have hbP : b ∉ P.asIdeal := fun h => hn (P.asIdeal.mul_mem_left _ h)
  have inj := IsFractionRing.injective (𝓞 E) E
  rw [ord_div P ((map_ne_zero_iff _ inj).2 ha0) ((map_ne_zero_iff _ inj).2 hb0),
    ord_algebraMap_eq_zero P haP, ord_algebraMap_eq_zero P hbP, sub_zero]

theorem ord_prod_primePow (P : HeightOneSpectrum (𝓞 E)) (T : Finset ℕ) (hT : ∀ ℓ ∈ T, ℓ.Prime)
    (k : ℕ → ℤ) {ℓ₀ : ℕ} (h0 : ℓ₀.Prime) (hm : (ℓ₀ : 𝓞 E) ∈ P.asIdeal) :
    ord P (((∏ ℓ ∈ T, (ℓ : ℚ) ^ k ℓ : ℚ) : E)) = if ℓ₀ ∈ T then k ℓ₀ * ord P (ℓ₀ : E) else 0 := by
  push_cast
  rw [ord_prod P _ _ (fun ℓ hℓ => zpow_ne_zero _ (Nat.cast_ne_zero.2 (hT ℓ hℓ).ne_zero))]
  rw [Finset.sum_congr rfl (g := fun ℓ => if ℓ₀ = ℓ then k ℓ * ord P (ℓ : E) else 0) ?_]
  · rw [Finset.sum_ite_eq]
  intro ℓ hℓ
  rw [ord_zpow P (Nat.cast_ne_zero.2 (hT ℓ hℓ).ne_zero)]
  split_ifs with h
  · subst h; rfl
  · rw [ord_natCast_coprime P h0 hm (by rwa [Nat.prime_dvd_prime_iff_eq h0 (hT ℓ hℓ)]), mul_zero]

theorem ord_primeMap_symm (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x) (P : HeightOneSpectrum (𝓞 E))
    (a : E) : ord P (τ a) = ord (primeMap τ P) a := by
  have := ord_primeMap τ (primeMap τ P) a
  rwa [primeMap_primeMap τ hτ] at this

theorem ord_eq_local (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x) (P : HeightOneSpectrum (𝓞 E))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : (ℓ : 𝓞 E) ∈ P.asIdeal) {l : E} (hl : l ≠ 0) {c : ℚ} {a : E}
    (hc : c ≠ 0) (ha : a ≠ 0) {d : ℕ} (hd : ¬ ℓ ∣ d)
    (h1 : IsIntegral ℤ ((d : E) * (l * ((c : E) * a * τ a)⁻¹)))
    (h2 : IsIntegral ℤ ((d : E) * ((c : E) * a * τ a) * l⁻¹)) :
    ord P l = ord P (c : E) + ord P a + ord (primeMap τ P) a := by
  have hd0 : (d : E) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; exact hd (dvd_zero _))
  have hc0 : (c : E) ≠ 0 := Rat.cast_ne_zero.2 hc
  have hta : τ a ≠ 0 := (map_ne_zero τ).2 ha
  have hy : (c : E) * a * τ a ≠ 0 := mul_ne_zero (mul_ne_zero hc0 ha) hta
  have o1 := ord_nonneg_of_isIntegral P h1
  have o2 := ord_nonneg_of_isIntegral P h2
  rw [ord_mul P hd0 (mul_ne_zero hl (inv_ne_zero hy)), ord_mul P hl (inv_ne_zero hy), ord_inv] at o1
  rw [ord_mul P (mul_ne_zero hd0 hy) (inv_ne_zero hl), ord_mul P hd0 hy, ord_inv] at o2
  have hdz : ord P (d : E) = 0 := ord_natCast_coprime P hℓ hP hd
  have hyv : ord P ((c : E) * a * τ a) = ord P (c : E) + ord P a + ord (primeMap τ P) a := by
    rw [ord_mul P (mul_ne_zero hc0 ha) hta, ord_mul P hc0 ha, ord_primeMap_symm τ hτ]
  linarith

theorem localDivisor : ∀ (E : Type) [Field E] [NumberField E] (τ : E ≃+* E), (∀ x, τ (τ x) = x) →
    ∀ (S : Finset ℕ) (l : E), l ≠ 0 → τ l = l →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (a : E), c ≠ 0 ∧ a ≠ 0 ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧
      IsIntegral ℤ ((d : E) * (l * ((c : E) * a * τ a)⁻¹)) ∧
      IsIntegral ℤ ((d : E) * ((c : E) * a * τ a) * l⁻¹)) →
    ∃ (c : ℚ) (f : HeightOneSpectrum (𝓞 E) → ℤ), c ≠ 0 ∧ (Function.support f).Finite ∧
      ∀ P : HeightOneSpectrum (𝓞 E), (∀ ℓ ∈ S, ℓ.Prime → ((ℓ : 𝓞 E) ∉ P.asIdeal)) →
        ord P l = ord P (c : E) + f P + f (primeMap τ P) := by
  intro E _ _ τ hτ S l hl _ H
  choose! cc aa hc0 ha0 dd hdd hI1 hI2 using H
  let rc : HeightOneSpectrum (𝓞 E) → ℕ := fun P => Classical.choose (exists_prime_mem P)
  have rc_prime : ∀ P, (rc P).Prime := fun P => (Classical.choose_spec (exists_prime_mem P)).1
  have rc_mem : ∀ P, ((rc P : ℕ) : 𝓞 E) ∈ P.asIdeal :=
    fun P => (Classical.choose_spec (exists_prime_mem P)).2
  have rc_map : ∀ P, rc (primeMap τ P) = rc P := fun P =>
    prime_eq_of_mem (primeMap τ P) (rc_prime _) (rc_prime P) (rc_mem _)
      (by rw [mem_primeMap, map_natCast]; exact rc_mem P)
  let T : Finset ℕ := (ord_finite l).toFinset.image rc
  have hT : ∀ ℓ ∈ T, ℓ.Prime := by
    intro ℓ hℓ
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.1 hℓ
    exact rc_prime P
  let k : ℕ → ℤ := fun ℓ => padicValRat ℓ (cc ℓ)
  let f : HeightOneSpectrum (𝓞 E) → ℤ := fun P => if rc P ∈ T then ord P (aa (rc P)) else 0
  refine ⟨∏ ℓ ∈ T, (ℓ : ℚ) ^ k ℓ, f, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun ℓ hℓ => zpow_ne_zero _ (Nat.cast_ne_zero.2 (hT ℓ hℓ).ne_zero)
  · refine (Set.Finite.biUnion T.finite_toSet fun ℓ _ => ord_finite (aa ℓ)).subset ?_
    intro P hP
    simp only [Function.mem_support, f] at hP
    split_ifs at hP with h
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe]
      exact ⟨rc P, h, hP⟩
    · exact absurd rfl hP
  · intro P hPS
    have hS : rc P ∉ S := fun h => hPS _ h (rc_prime P) (rc_mem P)
    rw [ord_prod_primePow P T hT k (rc_prime P) (rc_mem P)]
    have hfτ : f (primeMap τ P) = if rc P ∈ T then ord (primeMap τ P) (aa (rc P)) else 0 := by
      simp only [f, rc_map]
    rw [hfτ]
    simp only [f]
    split_ifs with h
    · rw [ord_eq_local τ hτ P (rc_prime P) (rc_mem P) hl (hc0 _ (rc_prime P) hS) (ha0 _ (rc_prime P) hS)
        (hdd _ (rc_prime P) hS) (hI1 _ (rc_prime P) hS) (hI2 _ (rc_prime P) hS),
        ord_ratCast P (rc_prime P) (rc_mem P) (hc0 _ (rc_prime P) hS)]
    · simp only [add_zero]
      by_contra hne
      exact h (Finset.mem_image.2 ⟨P, (ord_finite l).mem_toFinset.2 hne, rfl⟩)

end GlobalTheory.LocalDivisor

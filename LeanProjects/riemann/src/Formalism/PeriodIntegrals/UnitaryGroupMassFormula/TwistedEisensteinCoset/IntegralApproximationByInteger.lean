import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.UnitCongruentToInteger
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.UniformContinuityGaloisGroup

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

namespace NTA

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem iMul {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * r2, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [hs1 h, hs2 h]
  · simp only [map_mul]
    rw [← h1, ← h2]
    ring
theorem iAdd {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * s2 + r2 * s1, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [hs1 h, hs2 h]
  · simp only [map_mul, map_add]
    rw [← h1, ← h2]
    ring
theorem iSub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * s2 - r2 * s1, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [hs1 h, hs2 h]
  · simp only [map_mul, map_sub]
    rw [← h1, ← h2]
    ring
theorem iNat (m : ℕ) : IntAt P (m : E) := ⟨(m : 𝓞 E), 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩
theorem iPow {a : E} (ha : IntAt P a) (m : ℕ) : IntAt P (a ^ m) := by
  induction m with
  | zero => simpa using iNat P 1
  | succ m ih => rw [pow_succ]; exact iMul P ih ha
theorem iAlg (x : 𝓞 E) : IntAt P (algebraMap (𝓞 E) E x) := ⟨x, 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩

theorem qO_mem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal

theorem q_ne (hp : (Ideal.absNorm P.asIdeal).Prime) : (qOf P : E) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr hp.ne_zero

theorem one_nm : (1 : 𝓞 E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top

theorem not_int_inv_q (hp : (Ideal.absNorm P.asIdeal).Prime) : ¬ IntAt P ((qOf P : E)⁻¹) := by
  rintro ⟨r, s, hs, h⟩
  apply hs
  have hq := q_ne P hp
  have e : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((qOf P : ℕ) : 𝓞 E)) := by
    rw [map_mul, ← h, map_natCast, mul_assoc, inv_mul_cancel₀ hq, mul_one]
  rw [IsFractionRing.injective (𝓞 E) E e]
  exact Ideal.mul_mem_left _ _ (qO_mem P)

theorem natCast_notMem (hp : (Ideal.absNorm P.asIdeal).Prime) {m : ℕ} (hm : ¬ qOf P ∣ m) :
    (m : 𝓞 E) ∉ P.asIdeal := by
  intro hmP
  have hcop : IsCoprime ((qOf P : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  obtain ⟨u, v, huv⟩ := hcop
  apply one_nm P
  have e : (((u * ((qOf P : ℕ) : ℤ) + v * (m : ℤ) : ℤ)) : 𝓞 E) = 1 := by
    rw [huv]
    simp
  rw [← e]
  push_cast
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (qO_mem P)) (Ideal.mul_mem_left _ _ hmP)

theorem int_inv_nat (hp : (Ideal.absNorm P.asIdeal).Prime) {m : ℕ} (hm : ¬ qOf P ∣ m) : IntAt P ((m : E)⁻¹) := by
  have hm0 : (m : E) ≠ 0 := by
    have : m ≠ 0 := fun h => hm (h ▸ dvd_zero _)
    exact_mod_cast this
  refine ⟨1, (m : 𝓞 E), natCast_notMem P hp hm, ?_⟩
  rw [map_natCast, map_one, mul_inv_cancel₀ hm0]

theorem res_surj (hp : (Ideal.absNorm P.asIdeal).Prime) (x : 𝓞 E ⧸ P.asIdeal) :
    ∃ d : ℕ, d < qOf P ∧ Ideal.Quotient.mk P.asIdeal (d : 𝓞 E) = x := by
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
    unfold qOf
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ P.asIdeal) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let f : Fin (qOf P) → 𝓞 E ⧸ P.asIdeal := fun d => Ideal.Quotient.mk P.asIdeal ((d : ℕ) : 𝓞 E)
  have hinj : Function.Injective f := by
    intro d d' h
    have h' : ((d : ℕ) : 𝓞 E) - ((d' : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.Quotient.eq.mp h
    have hd := d.isLt
    have hd' := d'.isLt
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hm : ((d'.val - d.val : ℕ) : 𝓞 E) ∈ P.asIdeal := by
        rw [Nat.cast_sub hlt.le]
        have := P.asIdeal.neg_mem h'
        rwa [neg_sub] at this
      exact natCast_notMem P hp (fun hdvd => by
        have := Nat.le_of_dvd (by omega) hdvd
        omega) hm
    · have hm : ((d.val - d'.val : ℕ) : 𝓞 E) ∈ P.asIdeal := by
        rw [Nat.cast_sub hlt.le]
        exact h'
      exact natCast_notMem P hp (fun hdvd => by
        have := Nat.le_of_dvd (by omega) hdvd
        omega) hm
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨d, hd⟩ := hbij.2 x
  exact ⟨d.val, d.isLt, hd⟩

private theorem intAt_div_qOf_of_mem (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {α : 𝓞 E} (hα : α ∈ P.asIdeal) :
    IntAt P (algebraMap (𝓞 E) E α / (qOf P : E)) := by
  have hle : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr (qO_mem P)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro h
    apply hq
    have h2 : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right h
    exact h2 (Ideal.mem_span_singleton_self _)
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.mp hJP
  have hmem : α * t ∈ Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hα htJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hq0 := q_ne P hp
  refine ⟨c, t, htP, ?_⟩
  have e := congrArg (algebraMap (𝓞 E) E) hc
  simp only [map_mul, map_natCast] at e
  rw [mul_div_assoc', div_eq_iff hq0]
  unfold qOf
  linear_combination -e

theorem approx1 (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    {y : E} (hy : IntAt P y) : ∃ d : ℕ, d < qOf P ∧ IntAt P ((y - d) / (qOf P : E)) := by
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  obtain ⟨r, s, hs, hy'⟩ := hy
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨d, hdq, hd⟩ :=
    res_surj P hp (Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹)
  have hmem : r - (d : 𝓞 E) * s ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hd, mul_assoc, inv_mul_cancel₀ hs0,
      mul_one, sub_self]
  obtain ⟨c, t, ht, hct⟩ := intAt_div_qOf_of_mem P hp hq hmem
  have hs' : algebraMap (𝓞 E) E s ≠ 0 := by
    intro h
    apply hs
    rw [IsFractionRing.injective (𝓞 E) E (h.trans (map_zero _).symm)]
    exact P.asIdeal.zero_mem
  have hq0 := q_ne P hp
  refine ⟨d, hdq, c, t * s, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [ht h, hs h]
  · have hy2 : y = algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s := by
      rw [eq_div_iff hs', mul_comm]
      exact hy'
    rw [← hct, hy2, map_mul, map_sub, map_mul, map_natCast]
    field_simp

theorem mem_pow_of (hp : (Ideal.absNorm P.asIdeal).Prime) {α : 𝓞 E} {K : ℕ}
    (h : IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ K)) : α ∈ P.asIdeal ^ K := by
  haveI := P.isPrime
  obtain ⟨r, s, hs, h⟩ := h
  have hq0 := q_ne P hp
  have e : algebraMap (𝓞 E) E (s * α) = algebraMap (𝓞 E) E (r * ((qOf P : ℕ) : 𝓞 E) ^ K) := by
    rw [map_mul, map_mul, map_pow, map_natCast, ← h]
    field_simp
  have hsα : s * α ∈ P.asIdeal ^ K := by
    rw [IsFractionRing.injective (𝓞 E) E e]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (qO_mem P) K)
  exact (Ideal.IsPrime.mul_mem_pow P.asIdeal hsα).resolve_left hs

theorem exists_not_int (hp : (Ideal.absNorm P.asIdeal).Prime) {α : 𝓞 E} (hα : α ≠ 0) :
    ∃ K : ℕ, ¬ IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ K) := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ K, α ∈ P.asIdeal ^ K := fun K => mem_pow_of P hp (hcon K)
  have hbot := Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal P.isPrime.ne_top
  have hin : α ∈ (⨅ i, P.asIdeal ^ i) := Ideal.mem_iInf.mpr hall
  rw [hbot, Ideal.mem_bot] at hin
  exact hα hin

theorem decomp (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    {α : 𝓞 E} (hα : α ≠ 0) : ∃ (k : ℕ) (u : E), algebraMap (𝓞 E) E α = (qOf P : E) ^ k * u ∧ u ≠ 0 ∧
      IntAt P u ∧ IntAt P u⁻¹ := by
  classical
  have hex := exists_not_int P hp hα
  have hK : ¬ IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ Nat.find hex) := Nat.find_spec hex
  have hK0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hK
    rw [h0, pow_zero, div_one]
    exact iAlg P α
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hint : IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ k) :=
    not_not.mp (Nat.find_min hex (by omega : k < Nat.find hex))
  rw [hk] at hK
  have hq0 := q_ne P hp
  have hα' : algebraMap (𝓞 E) E α ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hα
  have hu0 : algebraMap (𝓞 E) E α / (qOf P : E) ^ k ≠ 0 := div_ne_zero hα' (pow_ne_zero _ hq0)
  refine ⟨k, algebraMap (𝓞 E) E α / (qOf P : E) ^ k, ?_, hu0, hint, ?_⟩
  · field_simp
  · obtain ⟨r, s, hs, hrs⟩ := hint
    have hrP : r ∉ P.asIdeal := by
      intro hr
      apply hK
      obtain ⟨c, t, ht, hct⟩ := intAt_div_qOf_of_mem P hp hq hr
      refine ⟨c, t * s, fun h => ?_, ?_⟩
      · rcases P.isPrime.mem_or_mem h with h | h
        exacts [ht h, hs h]
      · rw [← hct, ← hrs, map_mul]
        field_simp
        ring
    refine ⟨s, r, hrP, ?_⟩
    rw [← hrs, mul_assoc, mul_inv_cancel₀ hu0, mul_one]

theorem no_shift (hp : (Ideal.absNorm P.asIdeal).Prime) (d : ℕ) {w w' : E} (hw : w ≠ 0) (hwi : IntAt P w⁻¹)
    (hw' : IntAt P w') (h : w = (qOf P : E) ^ (d + 1) * w') : False := by
  have hq0 := q_ne P hp
  have hw'0 : w' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hw h
  have hint : IntAt P (w⁻¹ * w' * (qOf P : E) ^ d) :=
    iMul P (iMul P hwi hw') (iPow P (iNat P _) d)
  have e : w⁻¹ * w' * (qOf P : E) ^ d = (qOf P : E)⁻¹ := by
    rw [h]
    field_simp
    ring
  rw [e] at hint
  exact not_int_inv_q P hp hint

end NTA

open NTA in
theorem integer_integral_iff_dvd : IntegerIntegralIffDvd := by
  intro E _ _ P hp hq i e
  have hq0 := q_ne P hp
  constructor
  · intro hI
    by_contra hnd
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero _)
    obtain ⟨f, j, hj, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi0 (qOf P) hp.one_lt.ne'
    have hfe : f < e := by
      by_contra hfe
      push_neg at hfe
      exact hnd (Dvd.dvd.mul_right (pow_dvd_pow _ hfe) _)
    have h1 : IntAt P ((((qOf P ^ f * j : ℕ) : E) / (qOf P : E) ^ e) * (j : E)⁻¹ *
        (qOf P : E) ^ (e - f - 1)) :=
      iMul P (iMul P hI (int_inv_nat P hp hj)) (iPow P (iNat P _) _)
    have hj0 : (j : E) ≠ 0 := by
      have : j ≠ 0 := fun h => hj (h ▸ dvd_zero _)
      exact_mod_cast this
    have e2 : (((qOf P ^ f * j : ℕ) : E) / (qOf P : E) ^ e) * (j : E)⁻¹ * (qOf P : E) ^ (e - f - 1) =
        (qOf P : E)⁻¹ := by
      obtain ⟨g, rfl⟩ : ∃ g, e = f + g + 1 := ⟨e - f - 1, by omega⟩
      have hg : f + g + 1 - f - 1 = g := by omega
      rw [hg]
      push_cast
      field_simp
      ring
    rw [e2] at h1
    exact not_int_inv_q P hp h1
  · rintro ⟨k, rfl⟩
    have e2 : (((qOf P ^ e * k : ℕ) : E) / (qOf P : E) ^ e) = (k : E) := by
      push_cast
      field_simp
    rw [e2]
    exact iNat P k

open NTA in
theorem integral_approximation_by_integer : IntegralApproximationByInteger := by
  intro E _ _ P hp hq x N hx
  have hq0 := q_ne P hp
  induction N with
  | zero => exact ⟨0, by simp, by simpa using hx⟩
  | succ N ih =>
    obtain ⟨i, hi, hz⟩ := ih
    obtain ⟨d, hd, hzd⟩ := approx1 P hp hq hz
    refine ⟨i + d * qOf P ^ N, ?_, ?_⟩
    · calc i + d * qOf P ^ N < qOf P ^ N + d * qOf P ^ N := Nat.add_lt_add_right hi _
        _ = (d + 1) * qOf P ^ N := by ring
        _ ≤ qOf P * qOf P ^ N := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hd)
        _ = qOf P ^ (N + 1) := by ring
    · have e : (x - ((i + d * qOf P ^ N : ℕ) : E)) / (qOf P : E) ^ (N + 1) =
          ((x - i) / (qOf P : E) ^ N - d) / (qOf P : E) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact hzd

open NTA in
theorem element_eq_prime_power_mul_unit : ElementEqPrimePowerMulUnit := by
  intro E _ _ P hp hq a ha
  have hq0 := q_ne P hp
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨k, u, hu, hu0, hui, huii⟩ := decomp P hp hq hx0
  obtain ⟨k', u', hu', hu0', hui', huii'⟩ := decomp P hp hq hy0
  refine ⟨(k : ℤ) - k', u / u', ?_, div_ne_zero hu0 hu0', ?_, ?_⟩
  · rw [hu, hu', zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp
  · rw [div_eq_mul_inv]
    exact iMul P hui huii'
  · rw [inv_div, div_eq_mul_inv]
    exact iMul P hui' huii

open NTA in
theorem valuation_exponent_unique : ValuationExponentUnique := by
  intro E _ _ P hp hq e e' w w' hw hwi hwii hw'i hw'ii h
  have hq0 := q_ne P hp
  have hw' : w' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hw ((mul_eq_zero.mp h).resolve_left (zpow_ne_zero _ hq0))
  rcases lt_trichotomy e e' with hlt | heq | hgt
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d : ℕ, e' - e = (d : ℤ) + 1 := ⟨(e' - e - 1).toNat, by omega⟩
    apply no_shift P hp d hw hwii hw'i
    have hpw : (qOf P : E) ^ (d + 1) = (qOf P : E) ^ (e' - e) := by
      rw [hd, ← Nat.cast_succ, zpow_natCast]
    rw [hpw, zpow_sub₀ hq0, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hq0)]
    linear_combination h
  · exact heq
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d : ℕ, e - e' = (d : ℤ) + 1 := ⟨(e - e' - 1).toNat, by omega⟩
    apply no_shift P hp d hw' hw'ii hwi
    have hpw : (qOf P : E) ^ (d + 1) = (qOf P : E) ^ (e - e') := by
      rw [hd, ← Nat.cast_succ, zpow_natCast]
    rw [hpw, zpow_sub₀ hq0, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hq0)]
    linear_combination -h

open NTA in
theorem unit_congruent_to_integer : UnitCongruentToInteger := by
  intro E _ _ P hp hq w N hw hwi hwii
  have hq0 := q_ne P hp
  cases N with
  | zero => exact ⟨1, Nat.coprime_one_left _, by simpa using iSub P hwi (iNat P 1)⟩
  | succ N =>
    obtain ⟨i, hi, hI⟩ := integral_approximation_by_integer E P hp hq w (N + 1) hwi
    refine ⟨i, ?_, hI⟩
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_
    rintro ⟨j, rfl⟩
    apply not_int_inv_q P hp
    have h1 : IntAt P (w / (qOf P : E)) := by
      have e : w / (qOf P : E) = (w - ((qOf P * j : ℕ) : E)) / (qOf P : E) ^ (N + 1) *
          (qOf P : E) ^ N + (j : E) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact iAdd P (iMul P hI (iPow P (iNat P _) N)) (iNat P j)
    have e2 : (qOf P : E)⁻¹ = w / (qOf P : E) * w⁻¹ := by
      field_simp
    rw [e2]
    exact iMul P h1 hwii

end PI.TwistedEisensteinNonvanishing.W

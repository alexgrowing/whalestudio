import Formalism.PeriodIntegrals.TwNormLat

open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwNormLat.W

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem one_notMem' : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem mul_notMem' {s t : 𝓞 E} (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) : s * t ∉ P.asIdeal :=
  fun h => (P.isPrime.mem_or_mem h).elim hs ht

theorem intAt_alg (x : 𝓞 E) : IntAt P (algebraMap (𝓞 E) E x) :=
  ⟨x, 1, PI.TwNormLat.W.one_notMem' P, by simp⟩

theorem intAt_zero : IntAt P (0 : E) := by
  exact ⟨0, 1, PI.TwNormLat.W.one_notMem' P, by simp⟩

theorem intAt_one : IntAt P (1 : E) := by
  exact ⟨1, 1, PI.TwNormLat.W.one_notMem' P, by simp⟩

theorem intAt_natCast (k : ℕ) : IntAt P (k : E) := by
  exact ⟨k, 1, PI.TwNormLat.W.one_notMem' P, by simp⟩

theorem intAt_add {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨r * s' + s * r', s * s', PI.TwNormLat.W.mul_notMem' P hs hs', ?_⟩
  simp only [map_add, map_mul]
  rw [← h, ← h']
  ring

theorem intAt_mul {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨r * r', s * s', PI.TwNormLat.W.mul_notMem' P hs hs', ?_⟩
  simp only [map_mul]
  rw [← h, ← h']
  ring

theorem intAt_neg {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h⟩ := ha
  refine ⟨-r, s, hs, ?_⟩
  rw [map_neg, ← h]
  ring

theorem intAt_sub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  rw [sub_eq_add_neg]
  exact PI.TwNormLat.W.intAt_add P ha (PI.TwNormLat.W.intAt_neg P hb)

theorem intAt_pow {a : E} (ha : IntAt P a) (k : ℕ) : IntAt P (a ^ k) := by
  induction k with
  | zero => simpa using PI.TwNormLat.W.intAt_one P
  | succ k ih =>
    rw [pow_succ]
    exact PI.TwNormLat.W.intAt_mul P ih ha

theorem intAt_sum {ι : Type*} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (IntAt P) (fun _ _ ha hb => PI.TwNormLat.W.intAt_add P ha hb) (PI.TwNormLat.W.intAt_zero P) h

abbrev qE : E := ((Ideal.absNorm P.asIdeal : ℕ) : E)

theorem qE_ne_zero (hp : (Ideal.absNorm P.asIdeal).Prime) : qE P ≠ 0 := by
  show ((Ideal.absNorm P.asIdeal : ℕ) : E) ≠ 0
  exact Nat.cast_ne_zero.mpr hp.ne_zero

theorem uniform_continuity_galois_group (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {r : 𝓞 E} (hr : r ∈ P.asIdeal) :
    ∃ s t : 𝓞 E, s ∉ P.asIdeal ∧ t * ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) = s * r := by
  have hqP : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal
  have hle : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr hqP
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hJ'
    apply hq
    have hsq : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right hJ'
    exact hsq (Ideal.mem_span_singleton_self _)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.mp hJP
  have hmem : s * r ∈ Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} := by
    rw [hJ, mul_comm s r]
    exact Ideal.mul_mem_mul hr hsJ
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨s, t, hsP, ht⟩

theorem unit_of_not_div (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {y : E} (hy : IntAt P y)
    (hy' : ¬ IntAt P (y / qE P)) : IntAt P y⁻¹ := by
  obtain ⟨r, s, hs, h⟩ := hy
  by_cases hr : r ∈ P.asIdeal
  · exfalso
    obtain ⟨s', t, hs', ht⟩ := PI.TwNormLat.W.uniform_continuity_galois_group P hq hr
    apply hy'
    refine ⟨t, s * s', PI.TwNormLat.W.mul_notMem' P hs hs', ?_⟩
    have hq0 := PI.TwNormLat.W.qE_ne_zero P hp
    have ht' : algebraMap (𝓞 E) E t * qE P = algebraMap (𝓞 E) E s' * algebraMap (𝓞 E) E r := by
      have e := congrArg (algebraMap (𝓞 E) E) ht
      simpa using e
    rw [map_mul, mul_div_assoc', div_eq_iff hq0, ht', ← h]
    ring
  · refine ⟨s, r, hr, ?_⟩
    have hr0 : algebraMap (𝓞 E) E r ≠ 0 := by
      intro h0
      apply hr
      have hr' : r = 0 := IsFractionRing.injective (𝓞 E) E (by rw [h0, map_zero])
      rw [hr']
      exact P.asIdeal.zero_mem
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hr0
      rw [← h, mul_zero]
    rw [← h, mul_assoc, mul_inv_cancel₀ hy0, mul_one]

theorem mem_stdAt {n : ℕ} (v : Sp E n) : v ∈ stdAt E n P ↔ ∀ l, IntAt P (v l) := by
  change (∃ s ∈ P.asIdeal.primeCompl, s • v ∈ stdLat E n) ↔ _
  constructor
  · rintro ⟨s, hs, hv⟩ l
    have hl : (s • v) l ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_pi.mp hv l (Set.mem_univ l)
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hl
    refine ⟨r, s, hs, ?_⟩
    rw [hr, Pi.smul_apply, Algebra.smul_def]
  · intro h
    choose r s hs hrs using h
    refine ⟨∏ l, s l, Submonoid.prod_mem _ (fun l _ => hs l), ?_⟩
    refine Submodule.mem_pi.mpr fun l _ => ?_
    refine Submodule.mem_one.mpr ⟨(∏ l' ∈ Finset.univ.erase l, s l') * r l, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ l),
      map_mul, map_mul, ← hrs l]
    ring

theorem mem_lam (N c : ℕ) (v : Sp E (N + c)) :
    v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔ ∀ l, IntAt P (v l) := by
  show v ∈ Submodule.comap _ (stdAt E (N + c) P) ↔ _
  rw [Submodule.mem_comap, ← mem_stdAt P]
  refine Iff.of_eq (congrArg (· ∈ stdAt E (N + c) P) ?_)
  funext l
  simp [LocE.scE]

end PI.TwNormLat.W

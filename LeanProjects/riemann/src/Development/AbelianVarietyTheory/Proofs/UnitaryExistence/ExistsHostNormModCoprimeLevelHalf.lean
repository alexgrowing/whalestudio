import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

namespace GlobalTheory.NormMod

section Finite

variable {R : Type*} [CommRing R] [Finite R]

theorem exists_sq_sub_mul_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h0 : (p : R) = 0) {D ν : R}
    (hD : IsUnit D) (hν : IsUnit ν) : ∃ x y : R, x ^ 2 - D * y ^ 2 = ν := by
  obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
  have loc : ∀ m : MaximalSpectrum R, ∃ a b : R ⧸ m.asIdeal,
      a ^ 2 - Ideal.Quotient.mk _ D * b ^ 2 = Ideal.Quotient.mk _ ν := by
    intro m
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    haveI : Finite (R ⧸ m.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    letI : Fintype (R ⧸ m.asIdeal) := Fintype.ofFinite _
    have hp0 : (p : R ⧸ m.asIdeal) = 0 := by
      have := congrArg (Ideal.Quotient.mk m.asIdeal) h0
      simpa using this
    have hchar : ringChar (R ⧸ m.asIdeal) ≠ 2 := by
      intro h
      have h2 : ((2 : ℕ) : R ⧸ m.asIdeal) = 0 := by rw [← h]; exact ringChar.Nat.cast_ringChar
      rw [hj] at hp0
      push_cast at hp0 h2
      rw [h2] at hp0
      simp at hp0
    have hD' : Ideal.Quotient.mk m.asIdeal D ≠ 0 := (hD.map _).ne_zero
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (f := (Polynomial.X ^ 2 : Polynomial (R ⧸ m.asIdeal)))
      (g := Polynomial.C (-Ideal.Quotient.mk m.asIdeal D) * Polynomial.X ^ 2
        + Polynomial.C 0 * Polynomial.X + Polynomial.C (-Ideal.Quotient.mk m.asIdeal ν))
      (Polynomial.degree_X_pow 2) (Polynomial.degree_quadratic (neg_ne_zero.2 hD'))
      (FiniteField.odd_card_of_char_ne_two hchar)
    refine ⟨a, b, ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hab
    linear_combination hab
  choose a b hab using loc
  have hsurj : Function.Surjective
      (fun (x : R) (m : MaximalSpectrum R) => Ideal.Quotient.mk m.asIdeal x) :=
    fun f => by
      obtain ⟨x, hx⟩ := Ideal.pi_quotient_surjective
        (I := fun m : MaximalSpectrum R => m.asIdeal)
        (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) f
      exact ⟨x, funext hx⟩
  obtain ⟨x, hx⟩ := hsurj a
  obtain ⟨y, hy⟩ := hsurj b
  have hnil : IsNilpotent (x ^ 2 - D * y ^ 2 - ν) := by
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
    have := hab ⟨J, hm⟩
    rw [← hx, ← hy] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_pow]
    exact sub_eq_zero.2 this
  obtain ⟨μ, hμ⟩ := hν.exists_right_inv
  obtain ⟨k, hk⟩ := hnil
  set e := μ * (x ^ 2 - D * y ^ 2 - ν) with he
  have hek : e ^ p ^ k = 0 := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self (n := k) hp.one_lt).le
    rw [hc, pow_add, he, mul_pow, hk]
    ring
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (1 : R) e k
  rw [h0, hek] at hr
  obtain ⟨i, hi⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
  rw [hi] at hr
  refine ⟨x * (1 + e) ^ i, y * (1 + e) ^ i, ?_⟩
  have h1 : x ^ 2 - D * y ^ 2 = ν * (1 + e) := by
    rw [he]; linear_combination (-(x ^ 2 - D * y ^ 2 - ν)) * hμ
  linear_combination ((1 + e) ^ i) ^ 2 * h1 + ν * hr

theorem exists_pow_sub_one_mem (a : R) :
    ∃ k, 0 < k ∧ ∀ P : Ideal R, P.IsPrime → a ∉ P → a ^ k - 1 ∈ P := by
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧ a ^ i = a ^ j := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact ⟨i, j, h', h⟩
    · exact ⟨j, i, h', h.symm⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  refine ⟨k + 1, k.succ_pos, fun P hP ha => ?_⟩
  have : a ^ i * (a ^ (k + 1) - 1) ∈ P := by
    rw [show a ^ i * (a ^ (k + 1) - 1) = 0 by linear_combination -h]
    exact P.zero_mem
  exact (hP.mem_or_mem this).resolve_left fun h => ha (hP.mem_of_pow_mem _ h)

theorem exists_isUnit_neg (σ : R →+* R) (htop : Ideal.span {a | σ a = -a} = ⊤) :
    ∃ δ, σ δ = -δ ∧ IsUnit δ := by
  classical
  have key : ∀ s : Finset R, (∀ a ∈ s, σ a = -a) →
      ∃ δ, σ δ = -δ ∧ ∀ P : Ideal R, P.IsPrime → δ ∈ P → ∀ a ∈ s, a ∈ P := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp, by simp⟩
    | insert b s _ ih =>
      intro hs
      obtain ⟨δ, hδ, hP⟩ := ih fun a ha => hs a (Finset.mem_insert_of_mem ha)
      have hb := hs b (Finset.mem_insert_self _ _)
      obtain ⟨k, hk, hδk⟩ := exists_pow_sub_one_mem (δ ^ 2)
      refine ⟨δ + (1 - (δ ^ 2) ^ k) * b, ?_, fun P hp h => ?_⟩
      · simp only [map_add, map_mul, map_sub, map_pow, map_one, hδ, hb, neg_sq]
        ring
      · have h1 : δ ∈ P := by
          by_contra h1
          have h2 := hδk P hp fun h => h1 (hp.mem_of_pow_mem _ h)
          refine h1 ?_
          have := P.add_mem h (P.mul_mem_right b h2)
          convert this using 1
          ring
        have h2 : (δ ^ 2) ^ k ∈ P := P.pow_mem_of_mem (P.pow_mem_of_mem h1 2 two_pos) k hk
        have h3 : b ∈ P := by
          have := P.add_mem (P.sub_mem h h1) (P.mul_mem_right b h2)
          convert this using 1
          ring
        intro a ha
        rcases Finset.mem_insert.1 ha with rfl | ha
        · exact h3
        · exact hP P hp h1 a ha
  obtain ⟨δ, hδ, hP⟩ := key (Set.toFinite {a | σ a = -a}).toFinset (by simp)
  refine ⟨δ, hδ, ?_⟩
  by_contra hu
  obtain ⟨P, hmax, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  refine hmax.ne_top (top_le_iff.1 ?_)
  rw [← htop, Ideal.span_le]
  intro a ha
  exact hP P hmax.isPrime hmem a (by simpa using ha)

theorem exists_norm_eq (σ : R →+* R) (htop : Ideal.span {a | σ a = -a} = ⊤) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h0 : (p : R) = 0) {ν : R} (hν : IsUnit ν) (hfix : σ ν = ν) :
    ∃ t, t * σ t = ν := by
  obtain ⟨δ, hδ, hu⟩ := exists_isUnit_neg σ htop
  have unit : ∀ (a : R) (ha : σ a = a), IsUnit a →
      IsUnit (⟨a, ha⟩ : σ.eqLocus (RingHom.id R)) := by
    intro a ha h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have h2 := congrArg σ hb
    rw [map_mul, ha, map_one] at h2
    have h3 : σ b = b := by linear_combination b * h2 - σ b * hb
    exact IsUnit.of_mul_eq_one ⟨b, h3⟩ (Subtype.ext hb)
  have hD : σ (δ ^ 2) = δ ^ 2 := by rw [map_pow, hδ, neg_sq]
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, h⟩ := exists_sq_sub_mul_sq hp hp2
    (R := σ.eqLocus (RingHom.id R)) (Subtype.ext (by simpa using h0))
    (unit _ hD (hu.pow 2)) (unit _ hfix hν)
  have hx' : σ x = x := hx
  have hy' : σ y = y := hy
  have h' : x ^ 2 - δ ^ 2 * y ^ 2 = ν := congrArg Subtype.val h
  refine ⟨x + y * δ, ?_⟩
  rw [map_add, map_mul, hx', hy', hδ]
  linear_combination h'

end Finite

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HostModel
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem span_sub_bar : Ideal.span (Set.range fun b : 𝓞 E => b - H.bar b) = ⊤ := by
  haveI := H.unram
  let σ := IsCMField.ringOfIntegersComplexConj E
  have hσ : ∀ a, σ a = H.bar a := fun a => by
    apply RingOfIntegers.ext
    exact (IsCMField.coe_ringOfIntegersComplexConj E a).trans (H.bar_eq a).symm
  let L : 𝓞 E ⊗[𝓞 (maximalRealSubfield E)] 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E :=
    Algebra.TensorProduct.lift (AlgHom.id _ _) (σ : 𝓞 E →ₐ[_] 𝓞 E) fun _ _ => Commute.all _ _
  have hL : ∀ x y, L (x ⊗ₜ y) = x * H.bar y := fun x y => by simp [L, hσ]
  have h1 : ∀ z, Algebra.TensorProduct.lmul' (𝓞 (maximalRealSubfield E)) (S := 𝓞 E) z - L z ∈
      Ideal.span (Set.range fun b : 𝓞 E => b - H.bar b) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [hL, Algebra.TensorProduct.lmul'_apply_tmul, ← mul_sub]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨y, rfl⟩)
    | add x y hx hy =>
      rw [map_add, map_add]
      convert Ideal.add_mem _ hx hy using 1
      ring
  have h2 := congrArg L
    (Algebra.FormallyUnramified.one_tmul_mul_elem (R := 𝓞 (maximalRealSubfield E)) H.rt)
  rw [map_mul, map_mul, hL, hL, bar_rt, map_one] at h2
  have h3 : L (Algebra.FormallyUnramified.elem (𝓞 (maximalRealSubfield E)) (𝓞 E)) = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero : (2 : 𝓞 E) ≠ 0) (rt_ne_zero H))
    linear_combination -h2
  have h4 := h1 (Algebra.FormallyUnramified.elem (𝓞 (maximalRealSubfield E)) (𝓞 E))
  rw [h3, Algebra.FormallyUnramified.lmul_elem, sub_zero] at h4
  exact (Ideal.eq_top_iff_one _).2 h4

theorem exists_norm_mod_prime {p : ℕ} (hp : p.Prime) {ν : ℤ} (hν : IsCoprime ν (p : ℤ)) :
    ∃ t : 𝓞 E, (p : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨k, rfl⟩ : Odd ν := by
      rw [← Int.isCoprime_two_right]; simpa using hν
    exact ⟨1, -k, by simp⟩
  let I : Ideal (𝓞 E) := Ideal.span {(p : 𝓞 E)}
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let σ : 𝓞 E ⧸ I →+* 𝓞 E ⧸ I := Ideal.quotientMap I (H.bar : 𝓞 E →+* 𝓞 E) (by
    rw [Ideal.span_le]
    rintro _ rfl
    rw [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _)
  have hσ : ∀ a, σ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (H.bar a) := fun a => rfl
  have htop : Ideal.span {a | σ a = -a} = ⊤ := by
    rw [eq_top_iff, ← Ideal.map_top (Ideal.Quotient.mk I), ← span_sub_bar H, Ideal.map_span]
    refine Ideal.span_mono ?_
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    change σ _ = _
    rw [hσ, map_sub H.bar, bar_bar, ← map_neg, neg_sub]
  have h0 : (p : 𝓞 E ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have hu : IsUnit (ν : 𝓞 E ⧸ I) := by
    obtain ⟨a, b, hab⟩ := hν
    have := congrArg (Int.cast : ℤ → 𝓞 E ⧸ I) hab
    push_cast at this
    rw [h0] at this
    exact IsUnit.of_mul_eq_one (a : 𝓞 E ⧸ I) (by linear_combination this)
  obtain ⟨t, ht⟩ := exists_norm_eq σ htop hp hp2 h0 hu (map_intCast σ ν)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨t, ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hσ, ht,
    map_intCast, sub_self]

theorem exists_norm_mod_mul_prime {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) {ν : ℤ}
    (hν : IsCoprime ν (p : ℤ)) {t : 𝓞 E} (ht : (m : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E)) :
    ∃ s : 𝓞 E, ((m * p : ℕ) : 𝓞 E) ∣ s * H.bar s - (ν : 𝓞 E) ∧ (m : 𝓞 E) ∣ s - t := by
  obtain ⟨y, hy⟩ := ht
  by_cases hpm : p ∣ m
  · obtain ⟨c, hc⟩ := hpm
    have hc' : (m : 𝓞 E) = p * c := by exact_mod_cast hc
    have hy' : H.bar y = y := by
      have h := congrArg H.bar hy
      rw [map_sub, map_mul, bar_bar, map_intCast, map_mul, map_natCast] at h
      apply mul_left_cancel₀ (Nat.cast_ne_zero.2 hm : (m : 𝓞 E) ≠ 0)
      linear_combination hy - h
    obtain ⟨a, b, hab⟩ := hν
    have hab' := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at hab'
    refine ⟨t * (1 - m * y * a * H.w0), ⟨y * b - c * y * y * a
      + c * (y * a) ^ 2 * (H.w0 * (1 - H.w0)) * (t * H.bar t), ?_⟩, ⟨-(t * y * a * H.w0), by ring⟩⟩
    simp only [map_mul, map_sub, map_one, map_natCast, map_intCast, hy', cmHost_bar_halfIntegerGenerator]
    push_cast
    linear_combination (1 - m * y * a) * hy - m * y * hab'
      + (m * (-(y * y * a) + (y * a) ^ 2 * (H.w0 * (1 - H.w0)) * (t * H.bar t))) * hc'
  · obtain ⟨s, z, hz⟩ := exists_norm_mod_prime H hp hν
    have hco : IsCoprime (m : 𝓞 E) (p : 𝓞 E) :=
      ((Nat.coprime_comm.1 (hp.coprime_iff_not_dvd.2 hpm)).isCoprime.map
        (Int.castRingHom (𝓞 E))).imp fun a ⟨b, h⟩ => ⟨b, by simpa using h⟩
    obtain ⟨a, b, hab⟩ := id hco
    have cong : ∀ (k : ℕ) (u v : 𝓞 E), (k : 𝓞 E) ∣ u - v → (k : 𝓞 E) ∣ v * H.bar v - ν →
        (k : 𝓞 E) ∣ u * H.bar u - ν := by
      rintro k u v ⟨w, hw⟩ h
      have h2 := congrArg H.bar hw
      rw [map_sub, map_mul, map_natCast] at h2
      have := dvd_add h (Dvd.intro (w * H.bar u + v * H.bar w) rfl : (k : 𝓞 E) ∣ _)
      convert this using 1
      linear_combination H.bar u * hw + v * h2
    have d1 : (m : 𝓞 E) ∣ (b * p * t + a * m * s) - t :=
      ⟨a * (s - t), by linear_combination t * hab⟩
    have d2 : (p : 𝓞 E) ∣ (b * p * t + a * m * s) - s :=
      ⟨b * (t - s), by linear_combination s * hab⟩
    refine ⟨b * p * t + a * m * s, ?_, d1⟩
    push_cast
    exact hco.mul_dvd (cong _ _ _ d1 ⟨y, hy⟩) (cong _ _ _ d2 ⟨z, hz⟩)

theorem exists_norm_mod_mul {k : ℕ} (hk : k ≠ 0) {ν : ℤ} (hν : IsCoprime ν (k : ℤ)) :
    ∀ {m : ℕ}, m ≠ 0 → ∀ {t : 𝓞 E}, (m : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) →
      ∃ s : 𝓞 E, ((m * k : ℕ) : 𝓞 E) ∣ s * H.bar s - (ν : 𝓞 E) ∧ (m : 𝓞 E) ∣ s - t := by
  induction k using induction_on_primes with
  | zero => exact absurd rfl hk
  | one => exact fun _ t ht => ⟨t, by simpa using ht, by simp⟩
  | prime_mul p k hp ih =>
    intro m hm t ht
    push_cast at hν
    obtain ⟨s, hs, hst⟩ := exists_norm_mod_mul_prime H hm hp hν.of_mul_right_left ht
    obtain ⟨u, hu, hus⟩ := ih (right_ne_zero_of_mul hk) hν.of_mul_right_right
      (mul_ne_zero hm hp.ne_zero) hs
    refine ⟨u, by rwa [← mul_assoc], ?_⟩
    push_cast at hus
    simpa using dvd_add (dvd_of_mul_right_dvd hus) hst

theorem exists_norm_mod_level (l : Level H) (ν : ℤ) :
    ∃ t : 𝓞 E, (l.M : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) ∧ t - 1 ∈ l.Mb := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have ha' : H.bar a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ ha
  have hb' : H.bar b ∈ l.Mb := by
    obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hb
    simpa using hc
  have hab' := congrArg H.bar hab
  rw [map_add, map_one] at hab'
  refine ⟨b + ν * a, ?_, ?_⟩
  · rw [← Ideal.mem_span_singleton, ← l.prod]
    have h := Ideal.add_mem _
      (Ideal.mul_mem_left _ (1 - (ν : 𝓞 E)) (Ideal.mul_mem_mul hb' hb))
      (Ideal.mul_mem_left _ ((ν : 𝓞 E) ^ 2 - ν) (Ideal.mul_mem_mul ha ha'))
    convert h using 1
    rw [map_add, map_mul, map_intCast]
    linear_combination (ν : 𝓞 E) * (H.bar a + H.bar b) * hab + (ν : 𝓞 E) * hab'
  · convert l.Mb.mul_mem_left ((ν : 𝓞 E) - 1) ha using 1
    linear_combination hab

theorem exists_norm_mod (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (n : ℕ) (ν : ℤ) (hn : 0 < n) (hν : IsCoprime ν (n : ℤ)) :
    ∃ t : 𝓞 E, (n : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) ∧ (l.M ∣ n → t - 1 ∈ l.Mb) := by
  by_cases hM : l.M ∣ n
  · obtain ⟨k, rfl⟩ := hM
    obtain ⟨t, ht, ht1⟩ := exists_norm_mod_level H l ν
    push_cast at hν
    obtain ⟨s, hs, c, hc⟩ := exists_norm_mod_mul H (right_ne_zero_of_mul hn.ne')
      hν.of_mul_right_right (left_ne_zero_of_mul hn.ne') ht
    refine ⟨s, hs, fun _ => ?_⟩
    have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
      have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
      rw [← l.prod] at h
      exact (Ideal.mul_le_inf (I := l.Mb) h).1
    convert l.Mb.add_mem ht1 (l.Mb.mul_mem_right c hMb) using 1
    linear_combination hc
  · obtain ⟨s, hs, -⟩ := exists_norm_mod_mul H hn.ne' hν (m := 1) one_ne_zero (t := 1) (by simp)
    exact ⟨s, by simpa using hs, fun h => absurd h hM⟩

end GlobalTheory.NormMod

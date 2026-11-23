import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

namespace GlobalTheory.SimMult

section Ring

variable {O : Type*} [CommRing O] (σ : O →+* O)

theorem lift_step (hσ : ∀ x, σ (σ x) = x) {w : O} (hw : w + σ w = 1) (I : Ideal O) (ν μ : ℤ)
    (hμ : (ν : O) * μ - 1 ∈ I) (k : ℕ) (c : O) (hc : c * σ c - ν ∈ I ^ (k + 1)) :
    ∃ c', c' - c ∈ I ∧ c' * σ c' - ν ∈ I ^ (k + 2) := by
  set δ := c * σ c - ν with hδ
  have hI : δ ∈ I := Ideal.pow_le_self (by omega) hc
  have hσδ : σ δ = δ := by rw [hδ, map_sub, map_mul, hσ, map_intCast, mul_comm]
  refine ⟨c * (1 - w * δ * μ), ?_, ?_⟩
  · have : c * (1 - w * δ * μ) - c = (-c * w * μ) * δ := by ring
    rw [this]; exact I.mul_mem_left _ hI
  · have h1 : σ (c * (1 - w * δ * μ)) = σ c * (1 - σ w * δ * μ) := by
      simp only [map_mul, map_sub, map_one, hσδ, map_intCast]
    have h2 : c * (1 - w * δ * μ) * σ (c * (1 - w * δ * μ)) - ν
        = δ * (-((ν : O) * μ - 1) + (-μ + (ν + δ) * w * σ w * μ ^ 2) * δ) := by
      rw [h1]
      have h3 : c * σ c = ν + δ := by rw [hδ]; ring
      linear_combination ((1 - w * δ * μ) * (1 - σ w * δ * μ)) * h3 - (ν + δ) * δ * μ * hw
    rw [h2, pow_succ I (k + 1)]
    exact Ideal.mul_mem_mul hc (I.add_mem (I.neg_mem hμ) (I.mul_mem_left _ hI))

theorem lift_pow (hσ : ∀ x, σ (σ x) = x) {w : O} (hw : w + σ w = 1) (I : Ideal O) (ν μ : ℤ)
    (hμ : (ν : O) * μ - 1 ∈ I) (c : O) (hc : c * σ c - ν ∈ I) (k : ℕ) :
    ∃ c', c' - c ∈ I ∧ c' * σ c' - ν ∈ I ^ k := by
  have key : ∀ k, ∃ c', c' - c ∈ I ∧ c' * σ c' - ν ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨c, by simp, by simpa using hc⟩
    | succ k ih =>
      obtain ⟨c₁, h1, h2⟩ := ih
      obtain ⟨c₂, h3, h4⟩ := lift_step σ hσ hw I ν μ hμ k c₁ h2
      exact ⟨c₂, by simpa using I.add_mem h3 h1, h4⟩
  obtain ⟨c', h1, h2⟩ := key k
  exact ⟨c', h1, Ideal.pow_le_pow_right (Nat.le_succ k) h2⟩

theorem norm_congr (I : Ideal O) {c c' : O} (h : c' - c ∈ I) (h' : σ (c' - c) ∈ I) {ν : O}
    (hc : c * σ c - ν ∈ I) : c' * σ c' - ν ∈ I := by
  have : c' * σ c' - ν = (c * σ c - ν) + (σ c' * (c' - c) + c * σ (c' - c)) := by
    rw [map_sub]; ring
  rw [this]
  exact I.add_mem hc (I.add_mem (I.mul_mem_left _ h) (I.mul_mem_left _ h'))

end Ring

theorem exists_norm_finiteField {k : Type*} [Field k] [Finite k] (σ : k →+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ t, σ t ≠ t) (ν : ℤ) (hν : (ν : k) ≠ 0) :
    ∃ c, c * σ c = ν := by
  classical
  by_cases h2 : (2 : k) = 0
  · refine ⟨1, ?_⟩
    rcases Int.even_or_odd' ν with ⟨m, rfl | rfl⟩
    · exact absurd (by push_cast; rw [h2, zero_mul]) hν
    · push_cast; rw [h2]; simp
  obtain ⟨t, ht⟩ := hne
  set s := t - σ t with hs
  have hs0 : s ≠ 0 := sub_ne_zero.2 ht.symm
  have hσs : σ s = -s := by rw [hs, map_sub, hσ]; ring
  let F : Subfield k := σ.eqLocusField (RingHom.id k)
  let : Fintype F := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := by
    intro h
    apply h2
    have h3 : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).2 (by rw [h])
    have := congrArg F.subtype h3
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  let D : F := ⟨s * s, by
    change σ (s * s) = s * s
    rw [map_mul, hσs]; ring⟩
  have hD : D ≠ 0 := fun h => mul_ne_zero hs0 hs0 (congrArg Subtype.val h)
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2 - Polynomial.C (ν : F))
    (g := Polynomial.C (-D) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_sub_C (by norm_num) _)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 hD)) (FiniteField.odd_card_of_char_ne_two hF)
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul] at hab
  have h4 := congrArg F.subtype hab
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_intCast, map_zero,
    Subfield.coe_subtype, D] at h4
  have ha : σ (a : k) = a := a.2
  have hb : σ (b : k) = b := b.2
  refine ⟨a + b * s, ?_⟩
  rw [map_add, map_mul, ha, hb, hσs]
  linear_combination h4

section Dedekind

variable {O : Type*} [CommRing O] (σ : O →+* O)

theorem exists_norm_maximal (hσ : ∀ x, σ (σ x) = x) (P : Ideal O) [hP : P.IsMaximal]
    [Finite (O ⧸ P)] (hne : ∃ t, σ t - t ∉ P) (ν : ℤ) (hν : (ν : O) ∉ P) :
    ∃ c, c * σ c - ν ∈ P := by
  by_cases h : P ≤ P.comap σ
  · let := Ideal.Quotient.field P
    let τ : O ⧸ P →+* O ⧸ P := Ideal.quotientMap P σ h
    have hτ : ∀ x, τ (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (σ x) := fun x => rfl
    obtain ⟨c, hc⟩ := exists_norm_finiteField τ (by
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [hτ, hτ, hσ]) (by
        obtain ⟨t, ht⟩ := hne
        refine ⟨Ideal.Quotient.mk P t, fun h => ht ?_⟩
        rw [hτ] at h
        exact Ideal.Quotient.eq.1 h) ν (by
        intro h
        apply hν
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast]
        exact h)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨c, Ideal.Quotient.eq.1 ?_⟩
    rw [map_mul, map_intCast, ← hτ]
    exact hc
  · obtain ⟨x, hx, hx'⟩ := SetLike.not_le_iff_exists.1 h
    obtain ⟨y, e, he, hy⟩ := hP.exists_inv (x := σ x) hx'
    refine ⟨e + ν * (y * σ x), ?_⟩
    have hy' := congrArg σ hy
    rw [map_add, map_mul, hσ, map_one] at hy'
    have : (e + ν * (y * σ x)) * σ (e + ν * (y * σ x)) - ν
        = ((1 - ν) * σ (e + ν * (y * σ x))) * e + (ν * (ν - 1) * σ y) * x := by
      simp only [map_add, map_mul, map_intCast, hσ]
      linear_combination (ν * (σ e + ν * (σ y * x))) * hy + ν * hy'
    rw [this]
    exact P.add_mem (P.mul_mem_left _ he) (P.mul_mem_left _ hx)

theorem exists_norm_finset (hσ : ∀ x, σ (σ x) = x) (ν : ℤ) (S : Set (Ideal O)) (hS : S.Finite)
    (hmax : ∀ P ∈ S, P.IsMaximal) (hloc : ∀ P ∈ S, ∃ c, c * σ c - ν ∈ P) :
    ∃ c, ∀ P ∈ S, c * σ c - ν ∈ P := by
  have hsurj : Function.Surjective σ := fun x => ⟨σ x, hσ x⟩
  have hbij : Function.Bijective σ := ⟨Function.LeftInverse.injective hσ, hsurj⟩
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert P S hP hS ih =>
    obtain ⟨c, hc⟩ := ih (fun Q hQ => hmax Q (Set.mem_insert_of_mem _ hQ))
      (fun Q hQ => hloc Q (Set.mem_insert_of_mem _ hQ))
    by_cases hcP : c * σ c - ν ∈ P
    · exact ⟨c, fun Q hQ => by rcases hQ with rfl | hQ; exacts [hcP, hc Q hQ]⟩
    have hfix : σ (c * σ c - ν) = c * σ c - ν := by
      rw [map_sub, map_mul, hσ, map_intCast, mul_comm]
    obtain ⟨d, hd⟩ := hloc P (Set.mem_insert _ _)
    have hPm := hmax P (Set.mem_insert _ _)
    obtain ⟨y, e, he, hy⟩ := hPm.exists_inv hcP
    set δ := c * σ c - ν
    have hy' := congrArg σ hy
    rw [map_add, map_mul, hfix, map_one] at hy'

    refine ⟨d + (c - d) * (e * σ e), fun Q hQ => ?_⟩
    rcases hQ with rfl | hQ
    · refine norm_congr σ Q ?_ ?_ hd
      · rw [add_sub_cancel_left]
        exact Q.mul_mem_left _ (Q.mul_mem_right _ he)
      · rw [add_sub_cancel_left, map_mul, map_mul, hσ]
        exact Q.mul_mem_left _ (Q.mul_mem_left _ he)
    · have h1 : d + (c - d) * (e * σ e) - c = ((c - d) * (-y * σ e - σ y)) * δ := by
        linear_combination (c - d) * σ e * hy + (c - d) * hy'
      refine norm_congr σ Q ?_ ?_ (hc Q hQ)
      · rw [h1]; exact Q.mul_mem_left _ (hc Q hQ)
      · rw [h1, map_mul, hfix]; exact Q.mul_mem_left _ (hc Q hQ)

theorem exists_norm_mod [IsDedekindDomain O] [Module.Free ℤ O] [Module.Finite ℤ O] [CharZero O]
    (hσ : ∀ x, σ (σ x) = x) {w : O} (hw : w + σ w = 1)
    (hne : ∀ P : Ideal O, P.IsMaximal → ∃ t, σ t - t ∉ P) (n : ℕ) (hn : 0 < n) (ν : ℤ)
    (hν : IsCoprime ν (n : ℤ)) : ∃ c, (n : O) ∣ c * σ c - ν := by
  set J : Ideal O := Ideal.span {(n : O)}
  have hJ : J ≠ ⊥ := by
    simp only [J, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]; omega
  obtain ⟨μ, b, hμ⟩ := hν
  have hμ' : (ν : O) * μ - 1 ∈ J := by
    have := congrArg (Int.cast : ℤ → O) hμ
    push_cast at this
    exact Ideal.mem_span_singleton.2 ⟨-b, by linear_combination this⟩
  have hmax : ∀ P ∈ J.minimalPrimes, P.IsMaximal := fun P hP =>
    hP.1.1.isMaximal (fun h => hJ (le_bot_iff.1 (h ▸ hP.1.2)))
  obtain ⟨c, hc⟩ := exists_norm_finset σ hσ ν J.minimalPrimes
    (Ideal.finite_minimalPrimes_of_isNoetherianRing O J) hmax (by
      intro P hP
      have := hmax P hP
      have := Ideal.finiteQuotientOfFreeOfNeBot P (fun h => hJ (le_bot_iff.1 (h ▸ hP.1.2)))
      refine exists_norm_maximal σ hσ P (hne P (hmax P hP)) ν fun h => ?_
      apply (hmax P hP).ne_top
      rw [Ideal.eq_top_iff_one]
      have := P.sub_mem (P.mul_mem_right (μ : O) h) (hP.1.2 hμ')
      simpa using this)
  have hc' : c * σ c - ν ∈ J.radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Ideal.mem_sInf.2 fun {P} hP => hc P hP
  obtain ⟨k, hk⟩ := Ideal.exists_radical_pow_le_of_fg J (IsNoetherian.noetherian _)
  obtain ⟨c', -, h⟩ := lift_pow σ hσ hw J.radical ν μ (Ideal.le_radical hμ') c hc' k
  exact ⟨c', Ideal.mem_span_singleton.1 (hk h)⟩

end Dedekind

section Level

variable {O : Type*} [CommRing O] (σ : O →+* O)

theorem mem_sup_mul (J : Ideal O) {a b u v x : O} (h : u * a + v * b = 1)
    (ha : x ∈ J ⊔ Ideal.span {a}) (hb : x ∈ J ⊔ Ideal.span {b}) : x ∈ J ⊔ Ideal.span {a * b} := by
  obtain ⟨j, hj, y, hy, h1⟩ := Submodule.mem_sup.1 ha
  obtain ⟨j', hj', y', hy', h2⟩ := Submodule.mem_sup.1 hb
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨y', rfl⟩ := Ideal.mem_span_singleton'.1 hy'
  refine Submodule.mem_sup.2 ⟨u * a * j' + v * b * j, J.add_mem (J.mul_mem_left _ hj')
    (J.mul_mem_left _ hj), (u * y' + v * y) * (a * b), Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, ?_⟩
  linear_combination u * a * h2 + v * b * h1 + x * h

theorem mem_of_mul_eq_span {J K : Ideal O} {m : O} (h : J * K = Ideal.span {m}) : m ∈ J := by
  have h1 : m ∈ J * K := by rw [h]; exact Ideal.mem_span_singleton_self m
  have h2 : J * K ≤ J := Ideal.mul_le_inf.trans inf_le_left
  exact h2 h1

theorem mem_sup_of_coprime (J : Ideal O) {m n : ℕ} (hm : (m : O) ∈ J) (h : Nat.Coprime m n) (x : O) :
    x ∈ J ⊔ Ideal.span {(n : O)} := by
  obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := O) h
  refine Submodule.mem_sup.2 ⟨x * u * m, J.mul_mem_left _ hm, x * v * n,
    Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, ?_⟩
  linear_combination x * huv

theorem exists_norm_level (hσ : ∀ x, σ (σ x) = x) {w : O} (hw : w + σ w = 1) (ν : ℤ)
    (hnorm : ∀ n : ℕ, 0 < n → IsCoprime ν (n : ℤ) → ∃ c, (n : O) ∣ c * σ c - ν)
    (M A : ℕ) (J : Ideal O) (hprod : J * J.map σ = Ideal.span {(M : O)}) (hcop : J ⊔ J.map σ = ⊤)
    (hA : (A : ℤ) ∣ ν - 1) (n : ℕ) :
    0 < n → IsCoprime ν (n : ℤ) → ∃ c, (n : O) ∣ c * σ c - ν ∧ c - 1 ∈ J ⊔ Ideal.span {(n : O)} ∧
      c - 1 ∈ Ideal.span {(A : O)} ⊔ Ideal.span {(n : O)} := by
  have hMJ : (M : O) ∈ J := mem_of_mul_eq_span hprod
  have hA' : (A : O) ∣ ν - 1 := by
    have := map_dvd (Int.castRingHom O) hA
    simpa using this
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; omega
  | one => intro _ _; exact ⟨1, by simp, by simp, by simp⟩
  | prime_pow r k hr hk =>
    intro hn hν
    by_cases hM : r ∣ M
    · have h1 : IsCoprime (J ^ k) (J.map σ ^ k) := (Ideal.isCoprime_iff_sup_eq.2 hcop).pow
      obtain ⟨e', he', e, he, hee⟩ := Ideal.isCoprime_iff_exists.1 h1
      have hσe' : σ e' ∈ J.map σ ^ k := by
        rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem σ he'
      have hσe : σ e ∈ J ^ k := by
        have h2 := Ideal.mem_map_of_mem σ he
        have h3 : σ.comp σ = RingHom.id O := RingHom.ext hσ
        rwa [Ideal.map_pow, Ideal.map_map, h3, Ideal.map_id] at h2
      have hσee := congrArg σ hee
      rw [map_add, map_one] at hσee
      have hc1 : e + ν * e' - 1 = (ν - 1) * e' := by linear_combination hee
      refine ⟨e + ν * e', ?_, ?_, ?_⟩
      · have h4 : (e + ν * e') * σ (e + ν * e') - ν ∈ J ^ k * J.map σ ^ k := by
          have : (e + ν * e') * σ (e + ν * e') - ν
              = (1 - ν) * (σ e * e) + (ν * ν - ν) * (e' * σ e') := by
            rw [map_add, map_mul, map_intCast]
            linear_combination (ν * (σ e' + σ e)) * hee + ν * hσee
          rw [this]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hσe he))
            (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul he' hσe'))
        rw [← mul_pow, hprod, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h4
        refine dvd_trans ?_ h4
        rw [Nat.cast_pow]
        exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hM) k
      · rw [hc1]
        exact Ideal.mem_sup_left (J.mul_mem_left _ (Ideal.pow_le_self hk.ne' he'))
      · rw [hc1]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton.2 (hA'.mul_right _))
    have hMc : Nat.Coprime M (r ^ k) := ((Nat.Prime.coprime_iff_not_dvd hr).2 hM).symm.pow_right k
    by_cases hrA : r ∣ A
    · obtain ⟨c, h1, h2⟩ := lift_pow σ hσ hw (Ideal.span {(A : O)}) ν 1
        (by simpa [Ideal.mem_span_singleton] using hA') 1
        (by rw [Ideal.mem_span_singleton, map_one, one_mul]; exact dvd_sub_comm.1 hA') k
      refine ⟨c, ?_, mem_sup_of_coprime J hMJ hMc _, Ideal.mem_sup_left h1⟩
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
      refine dvd_trans ?_ h2
      rw [Nat.cast_pow]
      exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hrA) k
    · have hAc : Nat.Coprime A (r ^ k) :=
        ((Nat.Prime.coprime_iff_not_dvd hr).2 hrA).symm.pow_right k
      obtain ⟨c, hc⟩ := hnorm _ hn hν
      exact ⟨c, hc, mem_sup_of_coprime J hMJ hMc _,
        mem_sup_of_coprime _ (Ideal.mem_span_singleton_self _) hAc _⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ hν
    rw [Nat.cast_mul] at hν
    obtain ⟨c₁, h1, h2, h3⟩ := iha (by omega) hν.of_mul_right_left
    obtain ⟨c₂, h4, h5, h6⟩ := ihb (by omega) hν.of_mul_right_right
    have hco := Nat.Coprime.cast (R := O) hab
    obtain ⟨u, v, huv⟩ := hco
    have e1 : c₁ + (c₂ - c₁) * u * a - c₁ = (c₂ - c₁) * u * a := by ring
    have e2 : c₁ + (c₂ - c₁) * u * a - c₂ = (c₁ - c₂) * v * b := by
      linear_combination (c₂ - c₁) * huv
    have side : ∀ K : Ideal O, c₁ - 1 ∈ K ⊔ Ideal.span {(a : O)} →
        c₂ - 1 ∈ K ⊔ Ideal.span {(b : O)} →
        c₁ + (c₂ - c₁) * u * a - 1 ∈ K ⊔ Ideal.span {((a * b : ℕ) : O)} := by
      intro K k1 k2
      rw [Nat.cast_mul]
      refine mem_sup_mul K huv ?_ ?_
      · have := Ideal.add_mem _ k1 (Ideal.mem_sup_right (S := K)
          (Ideal.mem_span_singleton'.2 ⟨_, e1.symm⟩))
        convert this using 1; ring
      · have := Ideal.add_mem _ k2 (Ideal.mem_sup_right (S := K)
          (Ideal.mem_span_singleton'.2 ⟨_, e2.symm⟩))
        convert this using 1; ring
    refine ⟨c₁ + (c₂ - c₁) * u * a, ?_, side _ h2 h5, side _ h3 h6⟩
    rw [Nat.cast_mul]
    refine IsCoprime.mul_dvd ⟨u, v, huv⟩ ?_ ?_
    · rw [← Ideal.mem_span_singleton] at h1 ⊢
      refine norm_congr σ _ (Ideal.mem_span_singleton'.2 ⟨_, e1.symm⟩) ?_ h1
      rw [e1, map_mul, map_natCast]
      exact Ideal.mem_span_singleton'.2 ⟨_, rfl⟩
    · rw [← Ideal.mem_span_singleton] at h4 ⊢
      refine norm_congr σ _ (Ideal.mem_span_singleton'.2 ⟨_, e2.symm⟩) ?_ h4
      rw [e2, map_mul, map_natCast]
      exact Ideal.mem_span_singleton'.2 ⟨_, rfl⟩

end Level

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem exists_bar_sub_notMem (P : Ideal (𝓞 E)) (hP : P.IsMaximal) : ∃ t, H.bar t - t ∉ P := by
  by_contra hcon
  push Not at hcon
  have := H.unram
  let g : 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E :=
    { (H.bar : 𝓞 E →+* 𝓞 E) with
      commutes' := fun r => by
        apply RingOfIntegers.ext
        change ((H.bar (algebraMap _ _ r) : 𝓞 E) : E) = _
        rw [H.bar_eq]
        exact (IsCMField.complexConj E).commutes (r : maximalRealSubfield E) }
  have hg : g = AlgHom.id _ _ :=
    Algebra.FormallyUnramified.ext_of_iInf P (Ideal.iInf_pow_eq_bot_of_isDomain P hP.ne_top)
      fun x => Ideal.Quotient.eq.2 (hcon x)
  have h1 : H.bar H.rt = H.rt := congrArg (fun f => f H.rt) hg
  rw [HostModel.bar_rt] at h1
  have h2 : H.rt = 0 := by
    apply mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 E) ≠ 0)
    linear_combination -h1
  have h3 := H.rt_sq
  rw [h2] at h3
  have h4 : (H.d : 𝓞 E) = 0 := by linear_combination h3
  exact H.d_prime.ne_zero (by exact_mod_cast h4)

theorem exists_scalar (l : Level H) (n : ℕ) (hn : 0 < n) (hM : l.M ∣ n) (hAn : l.A ∣ n) (ν : ℤ)
    (hν : IsCoprime ν (n : ℤ)) (hA : (l.A : ℤ) ∣ ν - 1) :
    ∃ c : 𝓞 E, (n : 𝓞 E) ∣ c * H.bar c - ν ∧ c - 1 ∈ l.Mb ∧ (l.A : 𝓞 E) ∣ c - 1 := by
  have hσ : ∀ x, (H.bar : 𝓞 E →+* 𝓞 E) ((H.bar : 𝓞 E →+* 𝓞 E) x) = x := HostModel.bar_bar H
  have hw : H.w0 + (H.bar : 𝓞 E →+* 𝓞 E) H.w0 = 1 := by
    change H.w0 + H.bar H.w0 = 1
    rw [HostModel.cmHost_bar_halfIntegerGenerator]; ring
  obtain ⟨c, h1, h2, h3⟩ := exists_norm_level (H.bar : 𝓞 E →+* 𝓞 E) hσ hw ν
    (fun m hm h => exists_norm_mod _ hσ hw (exists_bar_sub_notMem H) m hm ν h)
    l.M l.A l.Mb l.prod l.coprime hA n hn hν
  have hMJ : (l.M : 𝓞 E) ∈ l.Mb :=
    mem_of_mul_eq_span l.prod
  refine ⟨c, h1, ?_, ?_⟩
  · refine (sup_le le_rfl ?_ : _ ≤ l.Mb) h2
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_of_dvd _ (Nat.cast_dvd_cast hM) hMJ
  · rw [← Ideal.mem_span_singleton]
    refine (sup_le le_rfl ?_ : _ ≤ Ideal.span {(l.A : 𝓞 E)}) h3
    exact Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hAn)

end Host

theorem exists_sim_trivial_of_mult :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (N : ℕ) (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) → ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (N : ℕ) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 → ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν ∧ (l.A : ℤ) ∣ g.ν l.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧ ∀ a, D.ModN l.A (g.f l.A a - a) := by
  intro hgrp hlift E _ _ _ H D l N ν hN hν hA
  have hMpos : 0 < l.M := by have := l.three_le; omega
  have hApos := l.A_pos
  by_cases hpq : 1 ≤ D.p + D.q
  swap
  · have := D.fin
    have := D.proj
    have : Subsingleton D.La := Module.finrank_zero_iff.1 (D.rank.trans (by norm_cast; omega))
    have hz : ∀ n x, D.ModN n x := fun n x => ⟨0, Subsingleton.elim _ _⟩
    refine ⟨⟨fun _ => LinearMap.id, fun _ => ν, fun _ _ _ _ _ => hz _ _,
      fun _ _ => ⟨LinearMap.id, fun _ => ⟨hz _ _, hz _ _⟩⟩, fun n _ a b => ?_⟩, by simp, hA,
      fun a => by rw [LinearMap.id_apply, sub_self]; exact Submodule.zero_mem _, fun a => hz _ _⟩
    rw [Subsingleton.elim a 0]; simp
  have hνA : IsCoprime ν (l.A : ℤ) := by
    obtain ⟨t, ht⟩ := hA
    exact ⟨1, -t, by linear_combination ht⟩
  obtain ⟨r, hr, hrp, hrν⟩ := Nat.forall_exists_prime_gt_and_zmodEq (N * l.M * l.A)
    (q := N * l.A) (a := ν) (by positivity) (by rw [Nat.cast_mul]; exact hν.mul_right hνA)
  have hn : 0 < N * l.M * l.A := by positivity
  have hrc : IsCoprime (r : ℤ) ((N * l.M * l.A : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hrp).2
      (Nat.not_dvd_of_pos_of_lt hn hr))
  have hd : ((N * l.A : ℕ) : ℤ) ∣ r - ν := hrν.symm.dvd
  have hdN : (N : ℤ) ∣ r - ν := dvd_trans (by push_cast; exact dvd_mul_right _ _) hd
  have hdA : (l.A : ℤ) ∣ r - 1 := by
    have h1 : (l.A : ℤ) ∣ r - ν := dvd_trans (by push_cast; exact dvd_mul_left _ _) hd
    simpa using dvd_add h1 hA
  obtain ⟨c, ⟨u, hu⟩, hcM, ⟨v, hv⟩⟩ := exists_scalar H l _ hn ⟨N * l.A, by ring⟩ ⟨N * l.M, by ring⟩
    r hrc hdA
  obtain ⟨g, hg, hgν⟩ := hlift E H D _ (c • LinearMap.id) r hn hrc (by
    intro a b
    refine ⟨D.EF a (u • b), ?_⟩
    have h1 : H.bar c • c • b = (r : ℤ) • b + ((N * l.M * l.A : ℕ) : ℤ) • u • b := by
      rw [← Int.cast_smul_eq_zsmul (𝓞 E), ← Int.cast_smul_eq_zsmul (𝓞 E), smul_smul, smul_smul,
        ← add_smul, Int.cast_natCast (N * l.M * l.A)]
      congr 1
      linear_combination hu
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [D.adj, h1, map_add, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul]
    ring)
  have hνg : ∀ m k : ℕ, 0 < m → 0 < k → N * l.M * l.A = m * k → (m : ℤ) ∣ g.ν m - r := by
    intro m k hm hk h
    have h1 := ((hgrp E H D hpq).1 g m k hm hk).1
    rw [h] at hgν
    have h2 : (m : ℤ) ∣ g.ν (m * k) - r := dvd_trans (by push_cast; exact dvd_mul_right _ _) hgν
    simpa using dvd_sub h2 h1
  have hfg : ∀ m k : ℕ, 0 < m → 0 < k → N * l.M * l.A = m * k → ∀ a, ∃ b,
      g.f m a - a = (c - 1) • a + (m : 𝓞 E) • b := by
    intro m k hm hk h a
    obtain ⟨b₁, h1⟩ := g.tower m k hm hk a
    obtain ⟨b₂, h2⟩ := hg a
    rw [h] at h2
    refine ⟨k • b₂ - b₁, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, smul_sub, smul_smul, ← h1, ← h2, sub_smul, one_smul]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    abel
  refine ⟨g, ?_, ?_, fun a => ?_, fun a => ?_⟩
  · simpa using dvd_add (hνg N (l.M * l.A) hN (by positivity) (by ring)) hdN
  · simpa using dvd_add (hνg l.A (N * l.M) hApos (by positivity) (by ring)) hdA
  · obtain ⟨b, hb⟩ := hfg l.M (N * l.A) hMpos (by positivity) (by ring) a
    rw [hb]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hcM Submodule.mem_top)
      (Submodule.smul_mem_smul
        (mem_of_mul_eq_span l.prod) Submodule.mem_top)
  · obtain ⟨b, hb⟩ := hfg l.A (N * l.M) hApos (by positivity) (by ring) a
    refine ⟨v • a + b, ?_⟩
    rw [hb, hv, ← Nat.cast_smul_eq_nsmul (𝓞 E), smul_add, smul_smul]

end GlobalTheory.SimMult

import Mathlib

open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset

namespace GlobalTheory

theorem sum_zeta_pow_succ_le (k : ℕ) {X : ℝ} (hX : 1 ≤ X) (N : ℕ) (hN : (N : ℝ) ≤ X) :
    ((∑ n ∈ Ioc 0 N, (ζ ^ (k + 1) : ArithmeticFunction ℕ) n : ℕ) : ℝ)
      ≤ N * (1 + Real.log X) ^ k := by
  have hL : 0 ≤ 1 + Real.log X := by have := Real.log_nonneg hX; linarith
  induction k generalizing N with
  | zero => simp only [zero_add, pow_one, ArithmeticFunction.sum_Ioc_zeta, pow_zero, mul_one, le_refl]
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.sum_Ioc_mul_eq_sum_sum, Nat.cast_sum]
    have hH : ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ ≤ 1 + Real.log X := by
      have h1 := harmonic_le_one_add_log N
      simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h1
      have h2 : Real.log N ≤ Real.log X := by
        rcases Nat.eq_zero_or_pos N with rfl | h
        · simpa using Real.log_nonneg hX
        · exact Real.log_le_log (by exact_mod_cast h) hN
      have h3 : Ioc 0 N = Icc 1 N := rfl
      rw [h3]; linarith
    calc _ ≤ ∑ n ∈ Ioc 0 N, (N * (1 + Real.log X) ^ k) * (n : ℝ)⁻¹ := by
          refine sum_le_sum fun n hn => ?_
          have hn0 : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
          rw [ArithmeticFunction.zeta_apply_ne hn0, one_mul]
          refine (ih (N / n) (le_trans (by exact_mod_cast Nat.div_le_self N n) hN)).trans ?_
          have : ((N / n : ℕ) : ℝ) ≤ N * (n : ℝ)⁻¹ := by
            rw [← div_eq_mul_inv]; exact Nat.cast_div_le
          calc _ ≤ (N * (n : ℝ)⁻¹) * (1 + Real.log X) ^ k := by gcongr
            _ = _ := by ring
      _ ≤ (N * (1 + Real.log X) ^ k) * (1 + Real.log X) := by
          rw [← mul_sum]; gcongr
      _ = _ := by ring

theorem sum_zeta_pow_le {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX : 1 ≤ X) :
    ((∑ n ∈ Ioc 0 ⌊X⌋₊, (ζ ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ)
      ≤ X * (1 + Real.log X) ^ (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hL : 0 ≤ 1 + Real.log X := by have := Real.log_nonneg hX; linarith
  have h := Nat.floor_le (zero_le_one.trans hX)
  refine (sum_zeta_pow_succ_le k hX _ h).trans ?_
  rw [Nat.add_sub_cancel]
  gcongr

theorem card_finMulAntidiag_eq_zeta_pow (k n : ℕ) :
    (Nat.finMulAntidiag k n).card = (ζ ^ k : ArithmeticFunction ℕ) n := by
  induction k generalizing n with
  | zero =>
    by_cases h : n = 1
    · subst h; simp [Nat.finMulAntidiag_one]
    · simp [Nat.finMulAntidiag_zero_left h, ArithmeticFunction.one_apply_ne h]
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.mul_apply]
    have : ∑ x ∈ n.divisorsAntidiagonal, (ζ : ArithmeticFunction ℕ) x.1 * (ζ ^ k : ArithmeticFunction ℕ) x.2
        = ∑ x ∈ n.divisorsAntidiagonal, (Nat.finMulAntidiag k x.2).card := by
      refine sum_congr rfl fun x hx => ?_
      rw [ArithmeticFunction.zeta_apply_ne (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx),
        one_mul, ih]
    rw [this, ← card_sigma]
    refine card_nbij' (fun f => ⟨(f 0, ∏ i, f (Fin.succ i)), fun i => f (Fin.succ i)⟩)
      (fun y => Fin.cons y.1.1 y.2) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [mem_coe, Nat.mem_finMulAntidiag, Fin.prod_univ_succ] at hf
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag]
      refine ⟨hf, trivial, ?_⟩
      intro h
      exact hf.2 (by rw [← hf.1, h, mul_zero])
    · rintro ⟨⟨a, b⟩, g⟩ hy
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at hy
      simp only [mem_coe, Nat.mem_finMulAntidiag, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [hy.2.1]; exact hy.1
    · intro f _
      exact Fin.cons_self_tail f
    · rintro ⟨⟨a, b⟩, g⟩ hy
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at hy
      simp only [Fin.cons_zero, Fin.cons_succ, hy.2.1]

variable (K : Type*) [Field K] [NumberField K]

theorem exists_colouring_maximal_ideals :
    ∃ c : Ideal (𝓞 K) → Fin (finrank ℚ K), ∀ p : ℕ, p.Prime → ∀ P Q : Ideal (𝓞 K),
      P.IsMaximal → Q.IsMaximal → (p : 𝓞 K) ∈ P → (p : 𝓞 K) ∈ Q → c P = c Q → P = Q := by
  classical
  haveI : Nonempty (Fin (finrank ℚ K)) := ⟨⟨0, finrank_pos⟩⟩
  have key : ∀ p : ℕ, ∃ e : Ideal (𝓞 K) → Fin (finrank ℚ K), p.Prime →
      Set.InjOn e {P | P.IsMaximal ∧ (p : 𝓞 K) ∈ P} := by
    intro p
    by_cases hp : p.Prime
    · have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
      haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
        ((Ideal.span_singleton_prime hp'.ne_zero).mpr hp').isMaximal hp0
      have hc := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hp0
      have hsub : {P : Ideal (𝓞 K) | P.IsMaximal ∧ (p : 𝓞 K) ∈ P} ⊆
          (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) : Set _) := by
        rintro P ⟨hP, hpP⟩
        rw [mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0]
        refine ⟨hP.isPrime, ⟨hmax.eq_of_le ?_ ?_⟩⟩
        · exact Ideal.comap_ne_top _ hP.ne_top
        · rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
          simpa using hpP
      obtain ⟨e, -, he⟩ := Set.Finite.exists_injOn_of_encard_le
        (t := (Set.univ : Set (Fin (finrank ℚ K))))
        (Finset.finite_toSet (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K))) (by
          rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_univ]
          simpa using hc)
      exact ⟨e, fun _ => he.mono hsub⟩
    · exact ⟨fun _ => Classical.arbitrary _, fun h => absurd h hp⟩
  choose e he using key
  have hmin : ∀ p : ℕ, p.Prime → ∀ P : Ideal (𝓞 K), P.IsMaximal → (p : 𝓞 K) ∈ P →
      (Ideal.absNorm P).minFac = p := by
    intro p hp P hP hpP
    obtain ⟨q, n, hn, hqP, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    rw [H, hq.pow_minFac hn.ne']
    by_contra hne
    have hco : IsCoprime (q : 𝓞 K) (p : 𝓞 K) :=
      Nat.Coprime.cast ((Nat.coprime_primes hq hp).mpr hne)
    obtain ⟨a, b, hab⟩ := hco
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr
      (hab ▸ P.add_mem (P.mul_mem_left a hqP) (P.mul_mem_left b hpP)))
  refine ⟨fun P => e (Ideal.absNorm P).minFac P, fun p hp P Q hP hQ hpP hpQ h => ?_⟩
  simp only [hmin p hp P hP hpP, hmin p hp Q hQ hpQ] at h
  exact he p hp ⟨hP, hpP⟩ ⟨hQ, hpQ⟩ h

theorem ncard_ideal_absNorm_eq_le {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard
      ≤ (ζ ^ finrank ℚ K : ArithmeticFunction ℕ) n := by
  classical
  obtain ⟨c, hc⟩ := exists_colouring_maximal_ideals K

  have key : ∀ (P : Ideal (𝓞 K)) (p f : ℕ), P.IsMaximal → p.Prime → (p : 𝓞 K) ∈ P →
      Ideal.absNorm P = p ^ f → ∀ s : Multiset (Ideal (𝓞 K)), (∀ Q ∈ s, Q.IsMaximal) →
      ((s.filter (fun Q => c Q = c P)).map Ideal.absNorm).prod ≠ 0 ∧
      (((s.filter (fun Q => c Q = c P)).map Ideal.absNorm).prod).factorization p
        = f * s.count P := by
    intro P p f hP hp hpP hN s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons Q s ih =>
      intro hs
      obtain ⟨ih0, ih⟩ := ih fun R hR => hs R (Multiset.mem_cons_of_mem hR)
      haveI hQ : Q.IsMaximal := hs Q (Multiset.mem_cons_self Q s)
      obtain ⟨q, g, hg, hqQ, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q
      have hQ0 : Ideal.absNorm Q ≠ 0 := H ▸ pow_ne_zero _ hq.ne_zero
      by_cases hcol : c Q = c P
      · rw [Multiset.filter_cons_of_pos (p := fun Q => c Q = c P) s hcol, Multiset.map_cons,
          Multiset.prod_cons, Nat.factorization_mul hQ0 ih0, Finsupp.add_apply, ih]
        refine ⟨mul_ne_zero hQ0 ih0, ?_⟩
        by_cases hQP : Q = P
        · subst hQP
          rw [Multiset.count_cons_self, hN, hp.factorization_pow, Finsupp.single_eq_same]
          ring
        · rw [Multiset.count_cons_of_ne (Ne.symm hQP), H, hq.factorization_pow,
            Finsupp.single_apply, if_neg, zero_add]
          rintro rfl
          exact hQP (hc q hq Q P hQ hP hqQ hpP hcol)
      · rw [Multiset.filter_cons_of_neg (p := fun Q => c Q = c P) s hcol]
        have hQP : P ≠ Q := by rintro rfl; exact hcol rfl
        rw [Multiset.count_cons_of_ne hQP]
        exact ⟨ih0, ih⟩
  have hprod : ∀ s : Multiset (Ideal (𝓞 K)),
      ∏ i, ((s.filter (fun Q => c Q = i)).map Ideal.absNorm).prod = Ideal.absNorm s.prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons Q s ih =>
      rw [Multiset.prod_cons, map_mul, ← ih]
      have : ∀ i, (((Q ::ₘ s).filter (fun Q => c Q = i)).map Ideal.absNorm).prod =
          (if c Q = i then Ideal.absNorm Q else 1) *
            ((s.filter (fun Q => c Q = i)).map Ideal.absNorm).prod := by
        intro i
        rw [Multiset.filter_cons]
        split_ifs <;> simp
      simp_rw [this]
      rw [prod_mul_distrib]
      simp
  have hmax : ∀ I : Ideal (𝓞 K), ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Q.IsMaximal := by
    intro I Q hQ
    have hQ' := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    exact (Ideal.isPrime_of_prime hQ').isMaximal hQ'.ne_zero
  have hne : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n → I ≠ ⊥ := by
    rintro I hI rfl
    exact hn (by rw [← hI]; simp)
  rw [← card_finMulAntidiag_eq_zeta_pow, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn
    (fun I i => (((UniqueFactorizationMonoid.normalizedFactors I).filter
      (fun Q => c Q = i)).map Ideal.absNorm).prod) ?_ ?_ (Finset.finite_toSet _)
  · intro I hI
    rw [mem_coe, Nat.mem_finMulAntidiag, hprod, Ideal.prod_normalizedFactors_eq_self (hne I hI)]
    exact ⟨hI, hn⟩
  · intro I hI J hJ h
    rw [← Ideal.prod_normalizedFactors_eq_self (hne I hI),
      ← Ideal.prod_normalizedFactors_eq_self (hne J hJ)]
    congr 1
    ext P
    by_cases hP : P.IsMaximal
    · obtain ⟨p, f, hf, hpP, hp, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
      have h1 := (key P p f hP hp hpP H _ (hmax I)).2
      have h2 := (key P p f hP hp hpP H _ (hmax J)).2
      have h3 := congrFun h (c P)
      simp only at h3
      rw [h3, h2] at h1
      exact (Nat.eq_of_mul_eq_mul_left hf h1).symm
    · rw [Multiset.count_eq_zero_of_notMem fun h => hP (hmax I P h),
        Multiset.count_eq_zero_of_notMem fun h => hP (hmax J P h)]

theorem two_pow_mul_factorial_succ_le (n : ℕ) :
    (2 : ℝ) ^ n * ((n + 1).factorial : ℝ) ≤ ((n : ℝ) + 1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb : 2 * ((n : ℝ) + 1) ^ (n + 1) ≤ ((n : ℝ) + 1 + 1) ^ (n + 1) := by
      have hpos : (0 : ℝ) < n + 1 := by positivity
      have h := one_add_mul_le_pow (a := ((n : ℝ) + 1)⁻¹) (by have := inv_pos.mpr hpos; linarith)
        (n + 1)
      have h1 : ((n + 1 : ℕ) : ℝ) * ((n : ℝ) + 1)⁻¹ = 1 := by push_cast; field_simp
      rw [h1] at h
      have h2 : ((n : ℝ) + 1 + 1) = (1 + ((n : ℝ) + 1)⁻¹) * (n + 1) := by field_simp
      rw [h2, mul_pow]
      gcongr
      linarith
    rw [Nat.factorial_succ (n + 1), pow_succ 2 n, pow_succ _ (n + 1)]
    push_cast
    have : (0 : ℝ) ≤ n + 1 + 1 := by positivity
    calc _ = (2 * (2 ^ n * ((n + 1).factorial : ℝ))) * ((n : ℝ) + 1 + 1) := by ring
      _ ≤ (2 * ((n : ℝ) + 1) ^ (n + 1)) * ((n : ℝ) + 1 + 1) := by gcongr
      _ ≤ _ := by gcongr

theorem minkowski_const_le_one :
    (4 / π) ^ InfinitePlace.nrComplexPlaces K *
      (((finrank ℚ K).factorial : ℝ) / (finrank ℚ K : ℝ) ^ finrank ℚ K) ≤ 1 := by
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hpos : 0 < finrank ℚ K := finrank_pos
  obtain ⟨n, hn⟩ : ∃ n, finrank ℚ K = n + 1 := ⟨finrank ℚ K - 1, by omega⟩
  rw [hn] at hr ⊢
  have h1 : (4 / π) ^ InfinitePlace.nrComplexPlaces K ≤ (2 : ℝ) ^ n := by
    have h4 : 4 / π ≤ 2 := by
      rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    calc _ ≤ (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K := by gcongr
      _ ≤ _ := pow_le_pow_right₀ one_le_two (by omega)
  have h2 := two_pow_mul_factorial_succ_le n
  rw [← mul_div_assoc, div_le_one (by positivity)]
  push_cast
  refine le_trans ?_ h2
  gcongr

theorem exists_ideal_in_class_of_norm_le_sqrt_discr (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ √|(discr K : ℝ)| := by
  obtain ⟨I, hI, hN⟩ := exists_ideal_in_class_of_norm_le C
  refine ⟨I, hI, hN.trans ?_⟩
  rw [← mul_assoc]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (minkowski_const_le_one K)

theorem one_le_sqrt_abs_discr : 1 ≤ √|(discr K : ℝ)| := by
  rw [Real.one_le_sqrt]
  exact_mod_cast Int.one_le_abs (discr_ne_zero K)

theorem classNumber_le_sqrt_discr_mul_pow_pred :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ (finrank ℚ K - 1) := by
  classical
  set X := √|(discr K : ℝ)| with hXdef
  have hX : 1 ≤ X := one_le_sqrt_abs_discr K
  refine le_trans ?_ (sum_zeta_pow_le (k := finrank ℚ K) finrank_pos hX)
  rw [Nat.cast_le]
  choose g hg hN using exists_ideal_in_class_of_norm_le_sqrt_discr K
  have hginj : Function.Injective fun C => (g C : Ideal (𝓞 K)) := by
    intro C D h
    rw [← hg C, ← hg D, Subtype.ext h]
  rw [classNumber, ← card_univ, card_eq_sum_card_fiberwise
    (f := fun C => Ideal.absNorm (g C : Ideal (𝓞 K))) (t := Ioc 0 ⌊X⌋₊)]
  · refine sum_le_sum fun n hn => le_trans ?_ (ncard_ideal_absNorm_eq_le K (mem_Ioc.mp hn).1.ne')
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard_of_injOn (fun C => (g C : Ideal (𝓞 K)))
      (fun C hC => by simpa using hC) hginj.injOn (Ideal.finite_setOfPred_absNorm_eq n)
  · intro C _
    rw [mem_coe, mem_Ioc]
    exact ⟨Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors _),
      Nat.le_floor (hN C)⟩

theorem classNumber_le_sqrt_discr_mul_pow :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ finrank ℚ K := by
  refine (classNumber_le_sqrt_discr_mul_pow_pred K).trans ?_
  have := Real.log_nonneg (one_le_sqrt_abs_discr K)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _))
    (Real.sqrt_nonneg _)

theorem classNumber_le_of_finrank_eq_two_mul {f : ℕ} (hf : finrank ℚ K = 2 * f) :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ (2 * f) :=
  hf ▸ classNumber_le_sqrt_discr_mul_pow K

end GlobalTheory

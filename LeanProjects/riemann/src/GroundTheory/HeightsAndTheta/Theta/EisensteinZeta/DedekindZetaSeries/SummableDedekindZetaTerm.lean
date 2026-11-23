import Mathlib
import GroundTheory.GlobalFields.TateThesis.PrimeZetaPole
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.DedekindZetaSeries.ZetaSevenHalves
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

namespace ZetaSevenHalvesBounds

variable (K : Type*) [Field K] [NumberField K]

def ratPrime (P : Ideal (𝓞 K)) : ℕ :=
  absNorm (under ℤ P)

variable {K}

theorem ratPrime_prime {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (ratPrime K P).Prime := by
  have : NeZero P := ⟨hP0⟩
  exact Nat.absNorm_under_prime P

theorem mem_primesOver_ratPrime {P : Ideal (𝓞 K)} (hP : P.IsPrime) :
    P ∈ primesOver (Ideal.span {((ratPrime K P : ℕ) : ℤ)}) (𝓞 K) :=
  ⟨hP, Int.liesOver_span_absNorm P⟩

theorem absNorm_eq_ratPrime_pow {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    absNorm P = ratPrime K P ^ (absNorm P).factorization (ratPrime K P) ∧
      0 < (absNorm P).factorization (ratPrime K P) := by
  have hp := ratPrime_prime hP hP0
  have : P.LiesOver (Ideal.span {((ratPrime K P : ℕ) : ℤ)}) := Int.liesOver_span_absNorm P
  have h := absNorm_eq_pow_inertiaDeg' P hp
  have hf : (absNorm P).factorization (ratPrime K P) =
      (Ideal.span {((ratPrime K P : ℕ) : ℤ)}).inertiaDeg' P := by
    rw [h, hp.factorization_pow, Finsupp.single_eq_same]
  refine ⟨hf ▸ h, ?_⟩
  rw [hf]
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, pow_zero, absNorm_eq_one_iff] at h
  exact hP.ne_top h

theorem natCard_primesOver_le {p : ℕ} (hp : p.Prime) :
    Nat.card (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) ≤ Module.finrank ℚ K := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) :=
    (IsDedekindDomain.primesOver_finite _ _).to_subtype
  let : Fintype (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← RingOfIntegers.rank K,
    ← Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K),
    Fintype.card_eq_sum_ones]
  refine Finset.sum_le_sum fun q _ => ?_
  have : q.1.IsPrime := q.2.1
  exact Right.one_le_mul (Ideal.ramificationIdx_pos (R := ℤ) q.1)
    (Ideal.inertiaDeg_pos (R := ℤ) q.1)

variable (K) in

def primeLabel (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K))
    (h : P ∈ primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) : Fin (Module.finrank ℚ K) :=
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) :=
    (IsDedekindDomain.primesOver_finite _ _).to_subtype
  Fin.castLE (natCard_primesOver_le hp) (Finite.equivFin _ ⟨P, h⟩)

theorem prime_label_injective {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (e : p = q) {P Q : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (Ideal.span {(p : ℤ)}) (𝓞 K))
    (hQ : Q ∈ primesOver (Ideal.span {(q : ℤ)}) (𝓞 K))
    (h : primeLabel K p hp P hP = primeLabel K q hq Q hQ) : P = Q := by
  subst e
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) :=
    (IsDedekindDomain.primesOver_finite _ _).to_subtype
  unfold primeLabel at h
  have h1 := Fin.castLE_injective _ h
  have h2 := (Finite.equivFin _).injective h1
  exact congrArg Subtype.val h2

theorem finrank_pos' : 0 < Module.finrank ℚ K := Module.finrank_pos

open Classical in
variable (K) in

def label (P : Ideal (𝓞 K)) : Fin (Module.finrank ℚ K) :=
  if h : P.IsPrime ∧ P ≠ ⊥ then
    primeLabel K (ratPrime K P) (ratPrime_prime h.1 h.2) P (mem_primesOver_ratPrime h.1)
  else ⟨0, finrank_pos'⟩

theorem label_inj {P Q : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : Q.IsPrime)
    (hQ0 : Q ≠ ⊥) (e : ratPrime K P = ratPrime K Q) (h : label K P = label K Q) : P = Q := by
  unfold label at h
  rw [dif_pos ⟨hP, hP0⟩, dif_pos ⟨hQ, hQ0⟩] at h
  exact prime_label_injective _ _ e _ _ h

variable (K) in

def tuple (I : Ideal (𝓞 K)) (j : Fin (Module.finrank ℚ K)) : ℕ :=
  ∏ P ∈ (normalizedFactors I).toFinset,
    if label K P = j then absNorm P ^ (normalizedFactors I).count P else 1

theorem prime_ne_bot_of_mem {I P : Ideal (𝓞 K)} (h : P ∈ normalizedFactors I) :
    P.IsPrime ∧ P ≠ ⊥ := by
  have hp := prime_of_normalized_factor P h
  exact ⟨(Ideal.prime_iff_isPrime hp.ne_zero).mp hp, hp.ne_zero⟩

theorem prod_tuple {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : ∏ j, tuple K I j = absNorm I := by
  classical
  unfold tuple
  rw [Finset.prod_comm]
  simp only [Finset.prod_ite_eq, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.prod_multiset_map_count, ← map_multiset_prod,
    associated_iff_eq.mp (prod_normalizedFactors hI)]

theorem factorization_tuple (I : Ideal (𝓞 K)) {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (tuple K I (label K P)).factorization (ratPrime K P) =
      (normalizedFactors I).count P * (absNorm P).factorization (ratPrime K P) := by
  classical
  unfold tuple
  rw [Nat.factorization_prod]
  swap
  · intro Q hQ
    split_ifs
    · refine pow_ne_zero _ ?_
      rw [Ne, absNorm_eq_zero_iff]
      exact (prime_ne_bot_of_mem (Multiset.mem_toFinset.mp hQ)).2
    · exact one_ne_zero
  rw [Finsupp.finset_sum_apply]
  have key : ∀ Q ∈ (normalizedFactors I).toFinset, Q ≠ P →
      (if label K Q = label K P then absNorm Q ^ (normalizedFactors I).count Q else 1).factorization
        (ratPrime K P) = 0 := by
    intro Q hQ hQP
    obtain ⟨hQp, hQ0⟩ := prime_ne_bot_of_mem (Multiset.mem_toFinset.mp hQ)
    split_ifs with hl
    · have hne : ratPrime K Q ≠ ratPrime K P := fun e => hQP (label_inj hQp hQ0 hP hP0 e hl)
      rw [Nat.factorization_pow, (absNorm_eq_ratPrime_pow hQp hQ0).1,
        (ratPrime_prime hQp hQ0).factorization_pow]
      simp [Finsupp.single_apply, hne]
    · simp
  rw [Finset.sum_eq_single P key]
  · rw [if_pos rfl, Nat.factorization_pow]
    simp
  · intro hPn
    rw [Multiset.mem_toFinset] at hPn
    rw [Multiset.count_eq_zero.mpr hPn]
    simp

theorem tuple_injOn : Set.InjOn (tuple K) {I | I ≠ ⊥} := by
  intro I hI J hJ h
  have hc : ∀ P, (normalizedFactors I).count P = (normalizedFactors J).count P := by
    intro P
    by_cases hP : P.IsPrime ∧ P ≠ ⊥
    · have hI' := factorization_tuple I hP.1 hP.2
      have hJ' := factorization_tuple J hP.1 hP.2
      rw [h] at hI'
      have hpos := (absNorm_eq_ratPrime_pow hP.1 hP.2).2
      exact Nat.eq_of_mul_eq_mul_right hpos (hI'.symm.trans hJ')
    · rw [Multiset.count_eq_zero.mpr fun hm => hP (prime_ne_bot_of_mem hm),
        Multiset.count_eq_zero.mpr fun hm => hP (prime_ne_bot_of_mem hm)]
  have hm : normalizedFactors I = normalizedFactors J := Multiset.ext.mpr hc
  rw [← associated_iff_eq.mp (prod_normalizedFactors hI),
    ← associated_iff_eq.mp (prod_normalizedFactors hJ), hm]

variable (K) in

theorem sum_rpow_neg_le_pow (T : Finset (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    ∑ I ∈ T, (absNorm I : ℝ) ^ (-s) ≤ (∑' m : ℕ, (m : ℝ) ^ (-s)) ^ Module.finrank ℚ K := by
  classical
  set g : ℕ → ℝ := fun m => (m : ℝ) ^ (-s) with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m => by positivity
  have hsum : Summable g := Real.summable_nat_rpow.mpr (by linarith)
  have hgz : g 0 = 0 := by simp [hg, Real.zero_rpow (by linarith : -s ≠ 0)]
  set T' := T.filter (· ≠ ⊥)
  have e1 : ∑ I ∈ T, g (absNorm I) = ∑ I ∈ T', g (absNorm I) := by
    refine (Finset.sum_filter_of_ne fun I _ hne => ?_).symm
    rintro rfl
    exact hne (by simp [hgz])
  have e2 : ∑ I ∈ T', g (absNorm I) = ∑ I ∈ T', ∏ j, g (tuple K I j) := by
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [← prod_tuple (Finset.mem_filter.mp hI).2]
    simp only [hg, Nat.cast_prod]
    rw [Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
  have e3 : ∑ I ∈ T', ∏ j, g (tuple K I j) = ∑ t ∈ T'.image (tuple K), ∏ j, g (t j) := by
    rw [Finset.sum_image]
    intro I hI J hJ h
    exact tuple_injOn (Finset.mem_filter.mp hI).2 (Finset.mem_filter.mp hJ).2 h
  set M := ∑ t ∈ T'.image (tuple K), ∑ j, t j + 1
  have hsub : T'.image (tuple K) ⊆ Fintype.piFinset fun _ => Finset.range M := by
    intro t ht
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range]
    have h1 : t j ≤ ∑ j, t j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : ∑ j, t j ≤ ∑ t ∈ T'.image (tuple K), ∑ j, t j :=
      Finset.single_le_sum (f := fun t : Fin (Module.finrank ℚ K) → ℕ => ∑ j, t j)
        (fun _ _ => Nat.zero_le _) ht
    omega
  calc ∑ I ∈ T, (absNorm I : ℝ) ^ (-s) = ∑ I ∈ T, g (absNorm I) := rfl
    _ = ∑ t ∈ T'.image (tuple K), ∏ j, g (t j) := by rw [e1, e2, e3]
    _ ≤ ∑ t ∈ Fintype.piFinset (fun _ => Finset.range M), ∏ j, g (t j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Finset.prod_nonneg fun _ _ => hg0 _)
    _ = (∑ m ∈ Finset.range M, g m) ^ Module.finrank ℚ K := (Finset.sum_pow' _ _ _).symm
    _ ≤ (∑' m, g m) ^ Module.finrank ℚ K :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => hg0 _)
          (hsum.sum_le_tsum _ fun _ _ => hg0 _) _

variable (K) in

theorem dedekindZetaReal_le_pow {s : ℝ} (hs : 1 < s) :
    GroundTheory.Global.dedekindZetaReal K s ≤ (∑' m : ℕ, (m : ℝ) ^ (-s)) ^ Module.finrank ℚ K := by
  refine Real.tsum_le_of_sum_range_le (fun n => GroundTheory.Global.dedekindZetaTerm_nonneg K s n)
    fun N => ?_
  rw [GroundTheory.Global.sum_range_dedekindZetaTerm]
  exact sum_rpow_neg_le_pow K _ hs

variable (K) in
theorem summable_dedekindZetaTerm {s : ℝ} (hs : 1 < s) :
    Summable (GroundTheory.Global.dedekindZetaTerm K s) := by
  refine summable_of_sum_range_le (c := (∑' m : ℕ, (m : ℝ) ^ (-s)) ^ Module.finrank ℚ K) (fun n => GroundTheory.Global.dedekindZetaTerm_nonneg K s n)
    fun N => ?_
  rw [GroundTheory.Global.sum_range_dedekindZetaTerm]
  exact sum_rpow_neg_le_pow K _ hs

theorem zetaSevenHalves_eq_tsum :
    zetaSevenHalves = ∑' m : ℕ, (m : ℝ) ^ (-(7 / 2 : ℝ)) := by
  have h := zeta_eq_tsum_one_div_nat_cpow (s := (7 / 2 : ℂ)) (by norm_num)
  have h2 : (∑' n : ℕ, 1 / (n : ℂ) ^ (7 / 2 : ℂ)) =
      ((∑' m : ℕ, (m : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    ext n
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.cpow_neg, one_div]
    push_cast
    rfl
  rw [zetaSevenHalves, h, h2, Complex.ofReal_re]

end ZetaSevenHalvesBounds

theorem DedekindBound.proof : ZetaSevenHalvesBounds.DedekindBound.Statement := by
  intro K _ _
  have h1 : (dedekindZeta K (7 / 2 : ℂ)).re = GroundTheory.Global.dedekindZetaReal K (7 / 2) := by
    have := GroundTheory.Global.dedekindZeta_ofReal K (s := 7 / 2) (by norm_num)
    push_cast at this
    rw [this, Complex.ofReal_re]
  have hle := ZetaSevenHalvesBounds.dedekindZetaReal_le_pow K (s := 7 / 2) (by norm_num)
  have hpos : 0 < GroundTheory.Global.dedekindZetaReal K (7 / 2) :=
    lt_of_lt_of_le one_pos (GroundTheory.Global.one_le_dedekindZetaReal
      (ZetaSevenHalvesBounds.summable_dedekindZetaTerm K (by norm_num)))
  rw [h1, ZetaSevenHalvesBounds.zetaSevenHalves_eq_tsum, ← Real.log_pow]
  exact Real.log_le_log hpos hle

end

end GroundTheory.Heights₂.Theta

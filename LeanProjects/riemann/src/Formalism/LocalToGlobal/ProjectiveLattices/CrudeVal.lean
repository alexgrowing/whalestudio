import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.Crude

open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
  {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K'] {ι : K →+* K'} {e : ℕ}

lemma crv_finite : Finite (𝓞 K ⧸ la.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot

theorem resCharOf_prime : (resCharOf la).Prime := by
  haveI := crv_finite la
  haveI : la.asIdeal.IsPrime := la.isPrime
  unfold resCharOf
  rcases CharP.char_is_prime_or_zero (𝓞 K ⧸ la.asIdeal) (ringChar (𝓞 K ⧸ la.asIdeal)) with hp | hp
  · exact hp
  · exact absurd hp (CharP.char_ne_zero_of_finite (𝓞 K ⧸ la.asIdeal) _)

lemma crv_char_mem : ((resCharOf la : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  unfold resCharOf
  exact ringChar.Nat.cast_ringChar

lemma crv_not_mem {m : ℕ} (hm : ¬ resCharOf la ∣ m) : ((m : ℕ) : 𝓞 K) ∉ la.asIdeal := by
  intro hmem
  apply hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hmem
  unfold resCharOf
  exact ringChar.dvd hmem

lemma crv_vLa_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : vLa la (x * y) = vLa la x + vLa la y := by
  unfold vLa
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]
  ring

lemma crv_vLa_pow {x : K} (hx : x ≠ 0) (k : ℕ) : vLa la (x ^ k) = k * vLa la x := by
  unfold vLa
  rw [map_pow, WithZero.log_pow]
  ring

lemma crv_vLa_natCast_eq (N : ℕ) : vLa la ((N : ℕ) : K) = -WithZero.log (la.intValuation (N : 𝓞 K)) := by
  unfold vLa
  rw [← map_natCast (algebraMap (𝓞 K) K) N, HeightOneSpectrum.valuation_of_algebraMap]

lemma crv_vLa_coprime {m : ℕ} (hm : ¬ resCharOf la ∣ m) : vLa la ((m : ℕ) : K) = 0 := by
  rw [crv_vLa_natCast_eq]
  have h1 : la.intValuation (m : 𝓞 K) = 1 := by
    rcases (la.intValuation_le_one (m : 𝓞 K)).lt_or_eq with hlt | heq
    · exact absurd ((la.intValuation_lt_one_iff_mem _).mp hlt) (crv_not_mem la hm)
    · exact heq
  rw [h1, WithZero.log_one, neg_zero]

lemma crv_vLa_char : vLa la ((resCharOf la : ℕ) : K) = ramOverZ la := by
  rw [crv_vLa_natCast_eq]
  unfold ramOverZ Ideal.ramificationIdx'
  have hr0 : ((resCharOf la : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (resCharOf_prime la).ne_zero
  have hv0 : la.intValuation ((resCharOf la : ℕ) : 𝓞 K) ≠ 0 := la.intValuation_ne_zero _ hr0
  have e1 : ∀ m : ℤ, la.intValuation ((resCharOf la : ℕ) : 𝓞 K) ≤ WithZero.exp m ↔
      WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K)) ≤ m := by
    intro m
    conv_lhs => rw [← WithZero.exp_log hv0]
    exact WithZero.exp_le_exp
  have key : ∀ n : ℕ, (Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((resCharOf la : ℕ) : ℤ)}) ≤
      la.asIdeal ^ n ↔ (n : ℤ) ≤ -WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K))) := by
    intro n
    rw [Ideal.map_span, Set.image_singleton, map_natCast, ← Ideal.dvd_iff_le,
      ← la.intValuation_le_pow_iff_dvd, e1]
    omega
  have hk : (0 : ℤ) ≤ -WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K)) := by
    exact_mod_cast (key 0).mp (by simp)
  have hS : {n : ℕ | Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((resCharOf la : ℕ) : ℤ)}) ≤
      la.asIdeal ^ n} = Set.Iic (-WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K))).toNat := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    rw [key]
    omega
  rw [hS, csSup_Iic]
  omega

lemma crv_vLa_natCast {N : ℕ} (hN : N ≠ 0) :
    vLa la ((N : ℕ) : K) = (padicValNat (resCharOf la) N * ramOverZ la : ℕ) := by
  have hp := resCharOf_prime la
  haveI : Fact (resCharOf la).Prime := ⟨hp⟩
  obtain ⟨n', hn'⟩ : resCharOf la ^ padicValNat (resCharOf la) N ∣ N := pow_padicValNat_dvd
  have hndvd : ¬ resCharOf la ∣ n' := by
    rintro ⟨b, rfl⟩
    have hd : resCharOf la ^ (padicValNat (resCharOf la) N + 1) ∣
        resCharOf la ^ padicValNat (resCharOf la) N * (resCharOf la * b) := ⟨b, by ring⟩
    rw [← hn'] at hd
    exact pow_succ_padicValNat_not_dvd (p := resCharOf la) hN hd
  have hn0 : n' ≠ 0 := by
    rintro rfl
    exact hN (by simpa using hn')
  have hK : ((N : ℕ) : K) = ((resCharOf la : ℕ) : K) ^ padicValNat (resCharOf la) N * ((n' : ℕ) : K) := by
    conv_lhs => rw [hn']
    push_cast
    ring
  have hp0 : ((resCharOf la : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hn0' : ((n' : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  rw [hK, crv_vLa_mul la (pow_ne_zero _ hp0) hn0', crv_vLa_pow la hp0, crv_vLa_coprime la hndvd,
    crv_vLa_char]
  push_cast
  ring

lemma crv_nval_natCast (ho : OverLa la V ι e) {N : ℕ} (hN : N ≠ 0) :
    nval V e ((N : ℕ) : K') = (((padicValNat (resCharOf la) N * ramOverZ la : ℕ) : ℝ) : EReal) := by
  unfold nval OverLa at *
  have hN' : ((N : ℕ) : K') ≠ 0 := by
    rw [← map_natCast ι N]
    exact (map_ne_zero ι).mpr (Nat.cast_ne_zero.mpr hN)
  rw [if_neg hN', ← map_natCast ι N, ho.2, crv_vLa_natCast la hN]
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  congr 1
  generalize padicValNat (resCharOf la) N * ramOverZ la = m
  push_cast
  rw [div_eq_iff he]
  ring

lemma crv_padic_prod {σ : Type} (p : ℕ) [Fact p.Prime] (α : σ →₀ ℕ) :
    padicValNat p (α.prod fun _ t => t.factorial) = ∑ s ∈ α.support, padicValNat p (α s).factorial := by
  classical
  simp only [Finsupp.prod]
  refine Finset.induction_on α.support ?_ ?_
  · simp
  · intro a u ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul (Nat.factorial_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _), ih]

lemma crv_legendre {σ : Type} (p : ℕ) [Fact p.Prime] (α : σ →₀ ℕ) :
    (p - 1) * padicValNat p (α.prod fun _ t => t.factorial) ≤ α.degree := by
  rw [crv_padic_prod, Finset.mul_sum]
  unfold Finsupp.degree
  exact Finset.sum_le_sum fun s _ => by
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _

theorem nval_factProd_le (ho : OverLa la V ι e) {σ : Type} (α : σ →₀ ℕ) :
    nval V e (((α.prod fun _ t => t.factorial : ℕ) : K')) ≤
      (((ramOverZ la : ℝ) * (α.degree : ℝ) / ((resCharOf la : ℝ) - 1) : ℝ) : EReal) := by
  have hp := resCharOf_prime la
  haveI : Fact (resCharOf la).Prime := ⟨hp⟩
  have hne : (α.prod fun _ t => t.factorial) ≠ 0 := by
    simp only [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _
  rw [crv_nval_natCast la ho hne, EReal.coe_le_coe_iff]
  have hleg := crv_legendre (resCharOf la) α
  have hp1 : (1 : ℝ) < resCharOf la := by exact_mod_cast hp.one_lt
  have hsub : ((resCharOf la - 1 : ℕ) : ℝ) = (resCharOf la : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hleg' : ((resCharOf la : ℝ) - 1) *
      (padicValNat (resCharOf la) (α.prod fun _ t => t.factorial) : ℝ) ≤ α.degree := by
    rw [← hsub]
    exact_mod_cast hleg
  rw [le_div_iff₀ (by linarith)]
  push_cast
  have hr : (0 : ℝ) ≤ ramOverZ la := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hleg' hr]

theorem nval_factProd_le_zero (ho : OverLa la V ι e) {σ : Type} (α : σ →₀ ℕ) (hα : ∀ s, α s < resCharOf la) :
    nval V e (((α.prod fun _ t => t.factorial : ℕ) : K')) ≤ 0 := by
  have hp := resCharOf_prime la
  haveI : Fact (resCharOf la).Prime := ⟨hp⟩
  have hne : (α.prod fun _ t => t.factorial) ≠ 0 := by
    simp only [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _
  have hv : padicValNat (resCharOf la) (α.prod fun _ t => t.factorial) = 0 := by
    rw [crv_padic_prod]
    refine Finset.sum_eq_zero fun s _ => padicValNat.eq_zero_of_not_dvd ?_
    rw [hp.dvd_factorial]
    exact not_le.mpr (hα s)
  rw [crv_nval_natCast la ho hne, hv]
  simp

end Formalism.L2.Pj.Crude

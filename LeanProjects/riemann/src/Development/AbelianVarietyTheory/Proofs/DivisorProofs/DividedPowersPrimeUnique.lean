import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.DivPowLPrime

theorem lPrime_eq_pow (l : ℕ) : lPrime l = l ^ lPrimeExp l := by
  unfold lPrime lPrimeExp; split_ifs with h <;> simp [h]

theorem one_le_lPrimeExp (l : ℕ) : 1 ≤ lPrimeExp l := by
  unfold lPrimeExp; split_ifs <;> norm_num

theorem isUnit_natCast_of_coprime {O : Type} [CommRing O] [IsLocalRing O] {l c : ℕ}
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hc : Nat.Coprime l c) : IsUnit (c : O) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  by_contra hu
  have hm : (c : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hu
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    have h := congrArg (Int.cast : ℤ → O) hab
    push_cast at h
    rw [← h]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hm)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

def factPrimePart (l m : ℕ) : ℕ := ordCompl[l] m.factorial

def qExp (l m : ℕ) : ℕ := lPrimeExp l * m - padicValNat l m.factorial

def qCoef (O : Type) [CommRing O] (l m : ℕ) : O :=
  (l : O) ^ qExp l m * Ring.inverse (factPrimePart l m : O)

theorem factorial_eq {l : ℕ} (hl : l.Prime) (m : ℕ) :
    m.factorial = l ^ padicValNat l m.factorial * factPrimePart l m := by
  rw [factPrimePart, ← Nat.factorization_def _ hl]
  exact (Nat.ordProj_mul_ordCompl_eq_self _ _).symm

section Lemmas

variable {O : Type} [CommRing O] [IsLocalRing O] {l : ℕ}

theorem isUnit_factPrimePart (hl : l.Prime) (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) (m : ℕ) :
    IsUnit (factPrimePart l m : O) :=
  isUnit_natCast_of_coprime hlO (Nat.coprime_ordCompl hl (Nat.factorial_ne_zero m))

theorem factorial_mul_qCoef (hl : l.Prime) (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) (m : ℕ)
    (hv : padicValNat l m.factorial ≤ lPrimeExp l * m) :
    (m.factorial : O) * qCoef O l m = (lPrime l : O) ^ m := by
  have hu := isUnit_factPrimePart hl hlO m
  have hf : (m.factorial : O) = (l : O) ^ padicValNat l m.factorial * (factPrimePart l m : O) := by
    have h := congrArg (Nat.cast : ℕ → O) (factorial_eq hl m)
    rwa [Nat.cast_mul, Nat.cast_pow] at h
  rw [hf, qCoef, qExp, lPrime_eq_pow, Nat.cast_pow, ← pow_mul]
  calc (l : O) ^ padicValNat l m.factorial * (factPrimePart l m : O) *
        ((l : O) ^ (lPrimeExp l * m - padicValNat l m.factorial) * Ring.inverse (factPrimePart l m : O))
      = (l : O) ^ (padicValNat l m.factorial + (lPrimeExp l * m - padicValNat l m.factorial)) *
          ((factPrimePart l m : O) * Ring.inverse (factPrimePart l m : O)) := by rw [pow_add]; ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ hu, Nat.add_sub_cancel' hv, mul_one]

theorem qCoef_eq_mul {m : ℕ} (h : lPrimeExp l ≤ qExp l m) :
    qCoef O l m = (lPrime l : O) * ((l : O) ^ (qExp l m - lPrimeExp l) * Ring.inverse (factPrimePart l m : O)) := by
  rw [qCoef, lPrime_eq_pow, Nat.cast_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

end Lemmas

theorem dividedPowers_lPrime : ∀ (l : ℕ), l.Prime → (∀ m : ℕ, (1 ≤ m → lPrimeExp l + padicValNat l m.factorial ≤ lPrimeExp l * m) ∧ m + 2 * padicValNat l m.factorial ≤ 2 * (lPrimeExp l * m)) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) → ∀ γ₀ : DividedPowers (Ideal.span {(l : R)}), (∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m) → ∃ γ : DividedPowers (Ideal.span {(lPrime l : R)}), (∀ m : ℕ, ∃ q : O, (m.factorial : O) * q = (lPrime l : O) ^ m ∧ ∀ x : R, γ.dpow m ((lPrime l : R) * x) = algebraMap O R q * x ^ m) ∧ (∀ (m : ℕ), ∀ y ∈ Ideal.span {(lPrime l : R)}, γ.dpow m y = γ₀.dpow m y) ∧ ∀ n : ℕ, 1 ≤ n → γ.IsSubDPIdeal (Ideal.span {(lPrime l : R) ^ n}) ∧ ∀ (r : ℕ) (m : Fin r → ℕ) (x : Fin r → R), (∀ i, x i ∈ Ideal.span {(lPrime l : R)}) → 2 * n * lPrimeExp l ≤ ∑ i, m i → ∏ i, γ.dpow (m i) (x i) ∈ Ideal.span {(lPrime l : R) ^ n} := by
  intro l hl hnum O _ _ _ _ hlO R _ _ htf γ₀ hγ₀
  have hv : ∀ m : ℕ, padicValNat l m.factorial ≤ lPrimeExp l * m := fun m => by
    have := (hnum m).2; generalize lPrimeExp l * m = a at *; omega
  have hq : ∀ m : ℕ, (m.factorial : O) * qCoef O l m = (lPrime l : O) ^ m := fun m =>
    factorial_mul_qCoef hl hlO m (hv m)
  have hqe : ∀ m : ℕ, 1 ≤ m → lPrimeExp l ≤ qExp l m := fun m hm => by
    have := (hnum m).1 hm; unfold qExp; generalize lPrimeExp l * m = a at *; omega
  have hle : Ideal.span {(lPrime l : R)} ≤ Ideal.span {(l : R)} := by
    refine Ideal.span_singleton_le_span_singleton.2 ⟨(l : R) ^ (lPrimeExp l - 1), ?_⟩
    rw [lPrime_eq_pow, Nat.cast_pow, ← pow_succ', Nat.sub_add_cancel (one_le_lPrimeExp l)]
  have hform0 : ∀ (m : ℕ) (x : R), γ₀.dpow m ((lPrime l : R) * x) = algebraMap O R (qCoef O l m) * x ^ m := by
    intro m x
    have hmem : (lPrime l : R) * x ∈ Ideal.span {(l : R)} :=
      hle (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    apply sub_eq_zero.1
    apply htf m.factorial _ (Nat.factorial_ne_zero m)
    rw [mul_sub, hγ₀ m _ hmem, ← mul_assoc, ← map_natCast (algebraMap O R) m.factorial, ← map_mul, hq m, map_pow,
      map_natCast, mul_pow, sub_self]
  have hsub : γ₀.IsSubDPIdeal (Ideal.span {(lPrime l : R)}) :=
    { isSubideal := hle
      dpow_mem := fun n hn j hj => by
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hj
        rw [mul_comm, hform0, qCoef_eq_mul (hqe n (by omega)), map_mul, map_natCast, mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _) }
  let γ := DividedPowers.IsSubDPIdeal.dividedPowers γ₀ hsub
  have hγeq : ∀ (m : ℕ), ∀ y ∈ Ideal.span {(lPrime l : R)}, γ.dpow m y = γ₀.dpow m y := fun m y hy =>
    DividedPowers.IsSubDPIdeal.dpow_eq_of_mem γ₀ hsub hy
  have hform : ∀ (m : ℕ) (x : R), γ.dpow m ((lPrime l : R) * x) = algebraMap O R (qCoef O l m) * x ^ m := by
    intro m x
    rw [hγeq m _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)), hform0]
  refine ⟨γ, fun m => ⟨qCoef O l m, hq m, hform m⟩, hγeq, fun n hn => ⟨?_, ?_⟩⟩
  · exact
    { isSubideal := Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ (by omega))
      dpow_mem := fun m hm j hj => by
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hj
        have hy : y * (lPrime l : R) ^ n = (lPrime l : R) * (y * (lPrime l : R) ^ (n - 1)) := by
          rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel hn]
        rw [hy, hform, qCoef_eq_mul (hqe m (by omega)), map_mul, map_natCast, mul_pow]
        apply Ideal.mem_span_singleton.2
        have h1 : n - 1 ≤ (n - 1) * m := Nat.le_mul_of_pos_right _ (by omega)
        have hd : (lPrime l : R) ^ n ∣ (lPrime l : R) * ((lPrime l : R) ^ (n - 1)) ^ m := by
          rw [← pow_mul, ← pow_succ']
          exact pow_dvd_pow _ (by omega)
        exact hd.trans (Dvd.intro (algebraMap O R ((l : O) ^ (qExp l m - lPrimeExp l) *
          Ring.inverse (factPrimePart l m : O)) * y ^ m) (by ring)) }
  · intro r m x hx hsum
    choose y hy using fun i => Ideal.mem_span_singleton'.1 (hx i)
    have hp : ∏ i, γ.dpow (m i) (x i) = algebraMap O R (∏ i, qCoef O l (m i)) * ∏ i, y i ^ m i := by
      rw [map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hy i, mul_comm, hform]
    have hprod : ∏ i, qCoef O l (m i) =
        (l : O) ^ (∑ i, qExp l (m i)) * ∏ i, Ring.inverse (factPrimePart l (m i) : O) := by
      simp only [qCoef, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have h2 : ∀ i, m i ≤ 2 * qExp l (m i) := fun i => by
      have := (hnum (m i)).2; unfold qExp; generalize lPrimeExp l * m i = a at *; omega
    have h3 : ∑ i, m i ≤ 2 * ∑ i, qExp l (m i) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => h2 i
    have hN : lPrimeExp l * n ≤ ∑ i, qExp l (m i) := by nlinarith
    rw [hp, Ideal.mem_span_singleton, hprod, map_mul, map_pow, map_natCast, lPrime_eq_pow, Nat.cast_pow, ← pow_mul]
    exact ((pow_dvd_pow _ hN).mul_right _).mul_right _

end GlobalTheory.DivPowLPrime

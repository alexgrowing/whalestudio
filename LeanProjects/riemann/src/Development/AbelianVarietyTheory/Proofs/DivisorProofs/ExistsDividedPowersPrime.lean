import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.TorsionFreeDividedPowers

open DividedPowers

def natPosSubmonoid (R : Type) [CommRing R] : Submonoid R where
  carrier := {r | ∃ k : ℕ, k ≠ 0 ∧ (k : R) = r}
  one_mem' := ⟨1, one_ne_zero, Nat.cast_one⟩
  mul_mem' := by
    rintro a b ⟨j, hj, rfl⟩ ⟨k, hk, rfl⟩
    exact ⟨j * k, Nat.mul_ne_zero hj hk, by push_cast; ring⟩

noncomputable def ofFactorialUnits {A : Type} [CommRing A] (h : ∀ n : ℕ, IsUnit (n.factorial : A))
    (J : Ideal A) : DividedPowers J where
  dpow           := OfInvertibleFactorial.dpow J
  dpow_null hx   := OfInvertibleFactorial.dpow_null hx
  dpow_zero hx   := OfInvertibleFactorial.dpow_zero hx
  dpow_one hx    := OfInvertibleFactorial.dpow_one hx
  dpow_mem hn hx := OfInvertibleFactorial.dpow_mem hn hx
  dpow_add {n} _ _ hx hy := OfInvertibleFactorial.dpow_add_of_lt (h _) (n.lt_succ_self) hx hy
  dpow_mul hx := OfInvertibleFactorial.dpow_mul hx
  mul_dpow {m} k _ hx := OfInvertibleFactorial.dpow_mul_of_add_lt (h _) (m + k).lt_succ_self hx
  dpow_comp hk hx := OfInvertibleFactorial.dpow_comp_of_mul_lt (h _) hk (lt_add_one _) hx

theorem ofFactorialUnits_dpow {A : Type} [CommRing A] (h : ∀ n : ℕ, IsUnit (n.factorial : A))
    (J : Ideal A) {n : ℕ} {x : A} (hx : x ∈ J) :
    (ofFactorialUnits h J).dpow n x = Ring.inverse (n.factorial : A) * x ^ n :=
  OfInvertibleFactorial.dpow_eq_of_mem hx

theorem exists_factorial_mul_eq (l : ℕ) (hl : l.Prime) {O : Type} [CommRing O] [IsLocalRing O]
    (hlm : (l : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) (hn : n ≠ 0) :
    ∃ q : O, (n.factorial : O) * q = (l : O) ^ (n - 1) := by
  haveI := Fact.mk hl
  have hN : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hfac := Nat.ordProj_mul_ordCompl_eq_self n.factorial l
  have hcop := Nat.coprime_ordCompl hl hN
  have hv : n.factorial.factorization l < n := by
    rw [Nat.factorization_def _ hl]
    exact padicValNat_factorial_lt_of_ne_zero l hn
  set v := n.factorial.factorization l
  set u := n.factorial / l ^ v
  have hu : IsUnit (u : O) := by
    by_contra hnu
    have hum : (u : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom O)
    simp only [eq_intCast, Int.cast_natCast] at hab
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hum)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨w, hw⟩ := hu
  refine ⟨(↑w⁻¹ : O) * (l : O) ^ (n - 1 - v), ?_⟩
  rw [← hfac]
  push_cast
  have e : (l : O) ^ v * (u : O) * ((↑w⁻¹ : O) * (l : O) ^ (n - 1 - v))
      = (l : O) ^ v * (l : O) ^ (n - 1 - v) * ((u : O) * ↑w⁻¹) := by ring
  rw [e, ← hw, Units.mul_inv, mul_one, ← pow_add, Nat.add_sub_cancel' (by omega)]

theorem exists_dividedPowers :
    ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R],
    (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) →
    ∃ γ₀ : DividedPowers (Ideal.span {(l : R)}), ∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)},
      (m.factorial : R) * γ₀.dpow m y = y ^ m := by
  intro l hl O _ _ _ _ hlm R _ _ htf
  let S := natPosSubmonoid R
  have hS : S ≤ nonZeroDivisors R := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_nonZeroDivisors_iff_left.mpr fun x hx => htf k x hk hx
  have hinj : Function.Injective (algebraMap R (Localization S)) :=
    IsLocalization.injective (Localization S) hS
  have hunit : ∀ n : ℕ, IsUnit (n.factorial : Localization S) := fun n => by
    have := IsLocalization.map_units (Localization S)
      (⟨(n.factorial : R), n.factorial, Nat.factorial_ne_zero n, rfl⟩ : S)
    simpa using this
  refine ⟨DividedPowers.ofInjective (Ideal.span {(l : R)}) (Ideal.span {(l : Localization S)})
    (algebraMap R (Localization S)) hinj (ofFactorialUnits hunit _) ?_ ?_,
    fun m y hy => DividedPowers.factorial_mul_dpow_eq_pow _ hy⟩
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
  · intro n x hx
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have hmem : algebraMap R (Localization S) (z * l) ∈ Ideal.span {(l : Localization S)} := by
      rw [map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    rw [ofFactorialUnits_dpow hunit _ hmem]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, fun h => absurd rfl h, by simp⟩
    · obtain ⟨q, hq⟩ := exists_factorial_mul_eq l hl hlm n hn.ne'
      refine ⟨algebraMap O R q * z ^ n * l,
        fun _ => Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
      rw [eq_comm, Ring.inverse_mul_eq_iff_eq_mul _ _ _ (hunit n)]
      have hq' : (n.factorial : R) * algebraMap O R q = (l : R) ^ (n - 1) := by
        have := congrArg (algebraMap O R) hq
        simpa using this
      have key : (n.factorial : R) * (algebraMap O R q * z ^ n * l) = (z * l) ^ n := by
        calc (n.factorial : R) * (algebraMap O R q * z ^ n * l)
            = ((n.factorial : R) * algebraMap O R q) * l * z ^ n := by ring
          _ = (z * l) ^ n := by
            rw [hq', ← pow_succ, Nat.sub_add_cancel hn, mul_pow, mul_comm]
      have := congrArg (algebraMap R (Localization S)) key
      simpa using this.symm

end GlobalTheory.TorsionFreeDividedPowers

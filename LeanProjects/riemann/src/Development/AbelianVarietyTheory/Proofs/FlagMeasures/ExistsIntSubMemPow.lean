import Mathlib

namespace GlobalTheory.IntSubMemPow

theorem exists_int_sub_mem {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (P : Ideal R)
    (hP : P ≠ ⊤) (hc : Nat.card (R ⧸ P) = p) (a : R) : ∃ m : ℤ, a - (m : R) ∈ P := by
  have : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  have : Finite (R ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)

  have hord : addOrderOf (1 : R ⧸ P) = p := by
    have hdvd : addOrderOf (1 : R ⧸ P) ∣ p := hc ▸ addOrderOf_dvd_natCard 1
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) one_ne_zero
    · exact h1

  have htop : AddSubgroup.zmultiples (1 : R ⧸ P) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, hc]
  have hmem : Ideal.Quotient.mk P a ∈ AddSubgroup.zmultiples (1 : R ⧸ P) := by
    rw [htop]; exact AddSubgroup.mem_top _
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine ⟨m, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, ← hm, zsmul_one, sub_self]

theorem span_sup_sq_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R)
    (hP : P.IsMaximal) (h0 : P ≠ ⊥) (x : R) (hx : x ∈ P) (hx2 : x ∉ P ^ 2) :
    Ideal.span {x} ⊔ P ^ 2 = P := by
  have hprime : Prime P := Ideal.prime_of_isPrime h0 hP.isPrime
  have hle : Ideal.span {x} ⊔ P ^ 2 ≤ P :=
    sup_le ((Ideal.span_singleton_le_iff_mem P).mpr hx) (Ideal.pow_le_self two_ne_zero)

  have hdvd : Ideal.span {x} ⊔ P ^ 2 ∣ P ^ 2 := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hprime 2).mp hdvd
  rw [associated_iff_eq] at hassoc
  interval_cases i
  · exfalso
    rw [pow_zero, Ideal.one_eq_top] at hassoc
    exact hP.ne_top (top_le_iff.mp (hassoc ▸ hle))
  · simpa using hassoc
  · exfalso
    exact hx2 (hassoc ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))

private lemma pow_le_span_pow_sup_pow_succ {R : Type} [CommRing R] (P : Ideal R) (x : R) (hx : x ∈ P)
    (h : Ideal.span {x} ⊔ P ^ 2 = P) (k : ℕ) :
    P ^ k ≤ Ideal.span {x ^ k} ⊔ P ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    refine Ideal.mul_le.mpr fun r hr s hs => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (ih hr)
    have hs' := hs
    rw [← h] at hs'
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hs'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hd
    have hsplit : (c * x ^ k + b) * (c' * x + e) =
        (c * c') * x ^ (k + 1) + (c * (x ^ k * e) + b * (c' * x + e)) := by ring
    rw [hsplit]
    refine Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) ?_
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) ?_
    · have : x ^ k * e ∈ P ^ k * P ^ 2 := Ideal.mul_mem_mul (Ideal.pow_mem_pow hx k) he
      rwa [← pow_add] at this
    · have : b * (c' * x + e) ∈ P ^ (k + 1) * P := Ideal.mul_mem_mul hb hs
      rwa [← pow_succ] at this

theorem exists_sub_mul_pow_mem {R : Type} [CommRing R] (P : Ideal R) (x : R) (hx : x ∈ P)
    (h : Ideal.span {x} ⊔ P ^ 2 = P) (k : ℕ) :
    ∀ y ∈ P ^ k, ∃ c : R, y - c * x ^ k ∈ P ^ (k + 1) := by
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (pow_le_span_pow_sup_pow_succ P x hx h k hy)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  exact ⟨c, by simpa using hb⟩

theorem exists_int_sub_mem_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : Nat.Prime p)
    (P : Ideal (NumberField.RingOfIntegers E)) (hP : Ideal.IsMaximal P)
    (hpP : (p : NumberField.RingOfIntegers E) ∈ P) (hN : Ideal.absNorm P = p)
    (hp2 : (p : NumberField.RingOfIntegers E) ∉ P ^ (2 : ℕ)) (k : ℕ)
    (a : NumberField.RingOfIntegers E) :
    ∃ m : ℤ, a - (m : NumberField.RingOfIntegers E) ∈ P ^ k := by
  have h0 : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hN
    exact hp.ne_zero hN.symm
  have hcard : Nat.card (NumberField.RingOfIntegers E ⧸ P) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hgen : Ideal.span {(p : NumberField.RingOfIntegers E)} ⊔ P ^ 2 = P := span_sup_sq_eq P hP h0 _ hpP hp2
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih

    obtain ⟨c, hc⟩ := exists_sub_mul_pow_mem P _ hpP hgen k _ hm
    obtain ⟨n, hn⟩ := exists_int_sub_mem hp P hP.ne_top hcard c
    refine ⟨m + n * (p : ℤ) ^ k, ?_⟩
    have hrest : (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k ∈ P ^ (k + 1) := by
      have : (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k ∈ P * P ^ k :=
        Ideal.mul_mem_mul hn (Ideal.pow_mem_pow hpP k)
      rwa [← pow_succ'] at this
    have heq : a - ((m + n * (p : ℤ) ^ k : ℤ) : NumberField.RingOfIntegers E) =
        (a - (m : NumberField.RingOfIntegers E) - c * (p : NumberField.RingOfIntegers E) ^ k) + (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k := by
      push_cast; ring
    rw [heq]
    exact Ideal.add_mem _ hc hrest

end GlobalTheory.IntSubMemPow

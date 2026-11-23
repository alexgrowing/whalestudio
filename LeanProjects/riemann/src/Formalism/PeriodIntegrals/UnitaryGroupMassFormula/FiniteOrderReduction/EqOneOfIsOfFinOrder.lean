import Mathlib

noncomputable section

namespace PI.FinOrdRedOne.Core

open Matrix Finset

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

def PDvd (q : R) (k : ℕ) (A : Matrix n n R) : Prop :=
  ∃ X : Matrix n n R, A = q ^ k • X

lemma pdvd_add {q : R} {k : ℕ} {A B : Matrix n n R} (hA : PDvd q k A) (hB : PDvd q k B) :
    PDvd q k (A + B) := by
  obtain ⟨X, rfl⟩ := hA
  obtain ⟨Y, rfl⟩ := hB
  exact ⟨X + Y, by rw [smul_add]⟩

lemma pdvd_zero (q : R) (k : ℕ) : PDvd q k (0 : Matrix n n R) := ⟨0, by rw [smul_zero]⟩

lemma pdvd_neg {q : R} {k : ℕ} {A : Matrix n n R} (hA : PDvd q k A) : PDvd q k (-A) := by
  obtain ⟨X, rfl⟩ := hA
  exact ⟨-X, by rw [smul_neg]⟩

lemma pdvd_mono {q : R} {k m : ℕ} (h : m ≤ k) {A : Matrix n n R} (hA : PDvd q k A) :
    PDvd q m A := by
  obtain ⟨X, rfl⟩ := hA
  refine ⟨q ^ (k - m) • X, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' h]

lemma pdvd_smul {q : R} {k : ℕ} {A : Matrix n n R} (c : R) (hA : PDvd q k A) :
    PDvd q k (c • A) := by
  obtain ⟨X, rfl⟩ := hA
  exact ⟨c • X, by rw [smul_comm]⟩

lemma pdvd_nsmul {q : R} {k : ℕ} {A : Matrix n n R} (c : ℕ) (hA : PDvd q k A) :
    PDvd q k (c • A) := by
  rw [← Nat.cast_smul_eq_nsmul R]
  exact pdvd_smul _ hA

lemma pdvd_sum {q : R} {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Matrix n n R)
    (h : ∀ i ∈ s, PDvd q k (f i)) : PDvd q k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (PDvd q k) (fun _ _ ha hb => pdvd_add ha hb) (pdvd_zero q k) h

lemma pdvd_pow_smul (q : R) (a m : ℕ) (X : Matrix n n R) :
    PDvd q (a * m) ((q ^ a • X) ^ m) :=
  ⟨X ^ m, by rw [smul_pow, ← pow_mul]⟩

lemma one_add_pow_eq (D : Matrix n n R) (k : ℕ) :
    (1 + D) ^ (k + 2) = ∑ i ∈ range (k + 1), (k + 2).choose (i + 2) • D ^ (i + 2)
      + (k + 2) • D + 1 := by
  rw [add_comm (1 : Matrix n n R) D, (Commute.one_right D).add_pow,
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [one_pow, mul_one, ← nsmul_eq_mul', Nat.choose_one_right, Nat.choose_zero_right,
    pow_zero, pow_one, one_smul, zero_add]

lemma smul_cancel [IsDomain R] {c : R} (hc : c ≠ 0) {X Y : Matrix n n R} (h : c • X = c • Y) :
    X = Y := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

theorem step [IsDomain R] (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hp0 : (p : R) ≠ 0)
    (hunit : ∀ l : ℕ, l.Prime → l ≠ p → IsUnit (l : R))
    (l : ℕ) (hl : l.Prime) (X : Matrix n n R) (a : ℕ) (ha : 1 ≤ a)
    (hpow : (1 + (p : R) ^ a • X) ^ l = 1) : PDvd (p : R) (a + 1) ((p : R) ^ a • X) := by
  set D : Matrix n n R := (p : R) ^ a • X with hD
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 2 := ⟨l - 2, by have := hl.two_le; omega⟩
  rw [one_add_pow_eq] at hpow
  set S := ∑ i ∈ range (k + 1), (k + 2).choose (i + 2) • D ^ (i + 2) with hS
  have hlin : (k + 2) • D = -S := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    have := congrArg (· - (1 : Matrix n n R)) hpow
    simpa only [add_sub_cancel_right, sub_self] using this
  by_cases hlp : k + 2 = p
  ·
    have hS2 : PDvd (p : R) (a + 2) S := by
      refine pdvd_sum _ _ fun i hi => ?_
      have hi' : i + 2 ≤ p := by rw [Finset.mem_range] at hi; omega
      rcases lt_or_eq_of_le hi' with hlt | heq
      · obtain ⟨c, hc⟩ := hp.dvd_choose_self (by omega : i + 2 ≠ 0) hlt
        rw [hlp, hc, mul_nsmul]
        refine pdvd_nsmul _ ?_
        rw [← Nat.cast_smul_eq_nsmul R]
        obtain ⟨Y, hY⟩ := pdvd_pow_smul (p : R) a (i + 2) X
        refine pdvd_mono (k := 1 + a * (i + 2)) (by nlinarith) ⟨Y, ?_⟩
        rw [hD, hY, smul_smul, ← pow_succ', add_comm]
      · refine pdvd_nsmul _ ?_
        refine pdvd_mono (k := a * (i + 2)) ?_ (pdvd_pow_smul (p : R) a (i + 2) X)
        rw [heq]; nlinarith
    have hpD : PDvd (p : R) (a + 2) ((p : R) • D) := by
      rw [← hlp] at hS2 ⊢
      have := pdvd_neg hS2
      rw [← hlin, ← Nat.cast_smul_eq_nsmul R] at this
      push_cast at this ⊢
      exact this
    obtain ⟨Y, hY⟩ := hpD
    refine ⟨Y, ?_⟩
    have hne : (p : R) ^ (a + 1) ≠ 0 := pow_ne_zero _ hp0
    have hXY : X = (p : R) • Y := by
      apply smul_cancel hne
      rw [hD, smul_smul, ← pow_succ'] at hY
      rw [hY, smul_smul, ← pow_succ]
    rw [hD, hXY, smul_smul, ← pow_succ]
  ·
    have hS1 : PDvd (p : R) (a + 1) S := by
      refine pdvd_sum _ _ fun i _ => pdvd_nsmul _ ?_
      exact pdvd_mono (k := a * (i + 2)) (by nlinarith) (pdvd_pow_smul (p : R) a (i + 2) X)
    obtain ⟨u, hu⟩ := hunit (k + 2) hl hlp
    have h1 : PDvd (p : R) (a + 1) (((k + 2 : ℕ) : R) • D) := by
      rw [Nat.cast_smul_eq_nsmul, hlin]
      exact pdvd_neg hS1
    have h2 := pdvd_smul ((u⁻¹ : Rˣ) : R) h1
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h2

theorem eq_one_of_pow_prime [IsDomain R] (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp0 : (p : R) ≠ 0) (hunit : ∀ l : ℕ, l.Prime → l ≠ p → IsUnit (l : R))
    (hsep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (A : Matrix n n R) (hA : PDvd (p : R) 1 (A - 1)) (l : ℕ) (hl : l.Prime) (hAl : A ^ l = 1) :
    A = 1 := by
  have key : ∀ a, 1 ≤ a → PDvd (p : R) a (A - 1) := by
    intro a ha
    induction a, ha using Nat.le_induction with
    | base => exact hA
    | succ a ha ih =>
      obtain ⟨X, hX⟩ := ih
      have hA' : A = 1 + (p : R) ^ a • X := by rw [← hX]; abel
      rw [hX]
      exact step p hp hp3 hp0 hunit l hl X a ha (hA' ▸ hAl)
  rw [← sub_eq_zero]
  ext i j
  rw [Matrix.zero_apply]
  apply hsep
  intro k
  obtain ⟨X, hX⟩ := key (k + 1) (by omega)
  rw [hX, Matrix.smul_apply, smul_eq_mul, pow_succ, mul_assoc]
  exact dvd_mul_right _ _

theorem isUnit_natCast_of_ne [IsLocalRing R] (p : ℕ) (hp : p.Prime)
    (hpM : (p : R) ∈ IsLocalRing.maximalIdeal R) (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) :
    IsUnit (l : R) := by
  by_contra h
  have hlM : (l : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact h
  have hcop : IsCoprime (l : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hl hp).mpr hlp)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : ((u : R) * l + (v : R) * p) = 1 := by
    have := congrArg (Int.cast : ℤ → R) huv
    push_cast at this
    exact this
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlM) (Ideal.mul_mem_left _ _ hpM)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr this)

theorem pdvd_of_map_residue [IsLocalRing R] (p : ℕ)
    (hM : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (A : Matrix n n R)
    (hA : A.map (IsLocalRing.residue R) = 1) : PDvd (p : R) 1 (A - 1) := by
  have h : ∀ i j, ∃ c : R, (A - 1) i j = (p : R) ^ 1 * c := by
    intro i j
    have hij := congrFun (congrFun hA i) j
    rw [map_apply, ← Matrix.map_one (IsLocalRing.residue R) (map_zero _) (map_one _),
      map_apply] at hij
    have hmem : A i j - (1 : Matrix n n R) i j ∈ IsLocalRing.maximalIdeal R :=
      Ideal.Quotient.eq.mp hij
    rw [hM, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, by rw [Matrix.sub_apply, ← hc, pow_one, mul_comm]⟩
  choose X hX using h
  exact ⟨Matrix.of X, by ext i j; rw [hX, Matrix.smul_apply, of_apply, smul_eq_mul]⟩

theorem eq_one_of_isOfFinOrder [IsDomain R] [IsLocalRing R] (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp0 : (p : R) ≠ 0) (hM : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)})
    (hsep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (β : GL n R) (hfin : IsOfFinOrder β)
    (hred : (β : Matrix n n R).map (IsLocalRing.residue R) = 1) : β = 1 := by
  have hpM : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [hM]; exact Ideal.mem_span_singleton_self _
  have hunit := isUnit_natCast_of_ne (R := R) p hp hpM
  by_contra hne
  set N := orderOf β with hN
  have hNpos : 0 < N := hfin.orderOf_pos
  have hN1 : N ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨l, hl, hld⟩ := Nat.exists_prime_and_dvd hN1
  set γ := β ^ (N / l) with hγ
  have hγl : γ ^ l = 1 := by
    rw [hγ, ← pow_mul, Nat.div_mul_cancel hld, hN, pow_orderOf_eq_one]
  have hγred : (γ : Matrix n n R).map (IsLocalRing.residue R) = 1 := by
    rw [hγ, Units.val_pow_eq_pow_val, ← RingHom.mapMatrix_apply, map_pow,
      RingHom.mapMatrix_apply, hred, one_pow]
  have hγ1 : (γ : Matrix n n R) = 1 := by
    refine eq_one_of_pow_prime p hp hp3 hp0 hunit hsep _ (pdvd_of_map_residue p hM _ hγred) l hl ?_
    rw [← Units.val_pow_eq_pow_val, hγl, Units.val_one]
  have hγ1' : γ = 1 := Units.ext hγ1
  have hdvd : N ∣ N / l := orderOf_dvd_of_pow_eq_one hγ1'
  have hpos : 0 < N / l := Nat.div_pos (Nat.le_of_dvd hNpos hld) hl.pos
  have hlt : N / l < N := Nat.div_lt_self hNpos hl.one_lt
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)

end PI.FinOrdRedOne.Core

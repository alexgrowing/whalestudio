import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

namespace LemGA

variable {LL : Type*} [Field LL] (v : AddValuation LL (WithTop ℚ))

theorem zero_lt_one' : (0 : WithTop ℚ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)

theorem one_lt_two' : (1 : WithTop ℚ) < 1 + 1 := by exact_mod_cast (by norm_num : (1 : ℚ) < 1 + 1)

theorem natCast_nonneg (n : ℕ) : 0 ≤ v (n : LL) := by
  induction n with
  | zero => rw [Nat.cast_zero, AddValuation.map_zero]; exact le_top
  | succ n ih =>
    rw [Nat.cast_succ]
    exact AddValuation.map_le_add v ih (by rw [AddValuation.map_one])

theorem intCast_nonneg (z : ℤ) : 0 ≤ v (z : LL) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · simpa using natCast_nonneg v n
  · rw [Int.cast_neg, AddValuation.map_neg]; simpa using natCast_nonneg v n

theorem natCast_coprime (l : ℕ) (hvl : v (l : LL) = 1) (n : ℕ) (hn : Nat.Coprime n l) :
    v (n : LL) = 0 := by
  have hb : ((Nat.gcd n l : ℕ) : ℤ) = n * Nat.gcdA n l + l * Nat.gcdB n l := Nat.gcd_eq_gcd_ab n l
  rw [show Nat.gcd n l = 1 from hn] at hb
  have h1 : (1 : LL) = (n : LL) * (Nat.gcdA n l : LL) + (l : LL) * (Nat.gcdB n l : LL) := by
    have := congrArg (fun z : ℤ => (z : LL)) hb
    push_cast at this
    exact this
  rcases (natCast_nonneg v n).lt_or_eq with hlt | heq
  · exfalso
    have h2 : 0 < v ((n : LL) * (Nat.gcdA n l : LL) + (l : LL) * (Nat.gcdB n l : LL)) := by
      apply AddValuation.map_lt_add
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le hlt (le_add_of_nonneg_right (intCast_nonneg v _))
      · rw [AddValuation.map_mul, hvl]
        exact lt_of_lt_of_le zero_lt_one' (le_add_of_nonneg_right (intCast_nonneg v _))
    rw [← h1, AddValuation.map_one] at h2
    exact lt_irrefl _ h2
  · exact heq.symm

theorem val_eq_zero_of_sub_one {y : LL} (h : 0 < v (y - 1)) : v y = 0 := by
  have := AddValuation.map_eq_of_lt_sub v (show v (1 : LL) < v (y - 1) by rwa [AddValuation.map_one])
  rwa [AddValuation.map_one] at this

theorem pow_sub_one_ge {y : LL} {a : WithTop ℚ} (ha : 0 < a) (h : v (y - 1) = a) (k : ℕ) :
    a ≤ v (y ^ k - 1) := by
  induction k with
  | zero => rw [pow_zero, sub_self, AddValuation.map_zero]; exact le_top
  | succ k ih =>
    have e : y ^ (k + 1) - 1 = y * (y ^ k - 1) + (y - 1) := by ring
    rw [e]
    apply AddValuation.map_le_add
    · rw [AddValuation.map_mul, val_eq_zero_of_sub_one v (by rw [h]; exact ha), zero_add]
      exact ih
    · rw [h]

theorem pow_coprime_val (l : ℕ) (hvl : v (l : LL) = 1) {y : LL} {a : WithTop ℚ} (ha : 0 < a)
    (h : v (y - 1) = a) (n : ℕ) (hn : Nat.Coprime n l) : v (y ^ n - 1) = a := by
  have e1 : y ^ n - 1 = (y - 1) * (∑ k ∈ Finset.range n, y ^ k) := by
    rw [mul_comm, geom_sum_mul]
  have e2 : (∑ k ∈ Finset.range n, y ^ k) = (n : LL) + ∑ k ∈ Finset.range n, (y ^ k - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  have hlt : v (n : LL) < v (∑ k ∈ Finset.range n, (y ^ k - 1)) := by
    rw [natCast_coprime v l hvl n hn]
    exact lt_of_lt_of_le ha (AddValuation.map_le_sum v (fun k _ => pow_sub_one_ge v ha h k))
  have hS : v (∑ k ∈ Finset.range n, y ^ k) = 0 := by
    rw [e2, AddValuation.map_add_eq_of_lt_left v hlt, natCast_coprime v l hvl n hn]
  rw [e1, AddValuation.map_mul, h, hS, add_zero]

theorem le_val_one_add_pow_sub (π : LL) (hπ0 : 0 ≤ v (1 + π)) {a : WithTop ℚ} (hπ : v π = a) (k : ℕ) :
    a + a ≤ v ((1 + π) ^ k - 1 - (k : LL) * π) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, sub_self, sub_zero, AddValuation.map_zero]
    exact le_top
  | succ k ih =>
    have e : (1 + π) ^ (k + 1) - 1 - ((k + 1 : ℕ) : LL) * π
        = (1 + π) * ((1 + π) ^ k - 1 - (k : LL) * π) + (k : LL) * (π * π) := by
      push_cast; ring
    rw [e]
    apply AddValuation.map_le_add
    · rw [AddValuation.map_mul]; exact le_trans ih (le_add_of_nonneg_left hπ0)
    · rw [AddValuation.map_mul, AddValuation.map_mul, hπ]
      exact le_add_of_nonneg_left (natCast_nonneg v k)

theorem pow_l_val (l : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (hvl : v (l : LL) = 1) {y : LL}
    {a : WithTop ℚ} (ha : 1 ≤ a) (h : v (y - 1) = a) : v (y ^ l - 1) = a + 1 := by
  obtain ⟨π, hπdef⟩ : ∃ π, π = y - 1 := ⟨_, rfl⟩
  have hy : y = 1 + π := by rw [hπdef]; ring
  subst hy
  have hπ : v π = a := by rw [← h, add_sub_cancel_left]
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one' ha
  have hy0 : v (1 + π) = 0 := val_eq_zero_of_sub_one v (by rw [h]; exact ha0)
  obtain ⟨t, ht⟩ : ∃ t, l = 2 * t + 1 := by
    rcases hl.eq_two_or_odd' with h2 | hodd
    · exact absurd h2 hl2
    · obtain ⟨t, ht⟩ := hodd; exact ⟨t, ht⟩
  have hsumN : (∑ i ∈ Finset.range l, i) = l * t := by
    have h2 := Finset.sum_range_id_mul_two l
    have hl1 : l - 1 = 2 * t := by omega
    rw [hl1] at h2
    have h3 : (∑ i ∈ Finset.range l, i) * 2 = (l * t) * 2 := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3
  have hsum : (∑ k ∈ Finset.range l, (k : LL)) = (l : LL) * t := by
    have := congrArg (Nat.cast : ℕ → LL) hsumN
    push_cast at this
    exact this
  have hk : ∀ k : ℕ, (1 + π) ^ k = 1 + π * (k : LL) + ((1 + π) ^ k - 1 - (k : LL) * π) :=
    fun k => by ring
  have eS : (∑ k ∈ Finset.range l, (1 + π) ^ k) = (l : LL) + (π * ((l : LL) * t)
      + ∑ k ∈ Finset.range l, ((1 + π) ^ k - 1 - (k : LL) * π)) := by
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, ← Finset.mul_sum, hsum, add_assoc]
  have h11 : (1 : WithTop ℚ) + 1 ≤ a + 1 := add_le_add ha (le_refl 1)
  have hB : v (l : LL) < v (π * ((l : LL) * t)
      + ∑ k ∈ Finset.range l, ((1 + π) ^ k - 1 - (k : LL) * π)) := by
    rw [hvl]
    apply AddValuation.map_lt_add
    · rw [AddValuation.map_mul, AddValuation.map_mul, hvl, hπ]
      refine lt_of_lt_of_le one_lt_two' (le_trans h11 ?_)
      exact add_le_add (le_refl a) (le_add_of_nonneg_right (natCast_nonneg v t))
    · refine lt_of_lt_of_le one_lt_two' (le_trans (add_le_add ha ha) ?_)
      exact AddValuation.map_le_sum v (fun k _ => le_val_one_add_pow_sub v π (le_of_eq hy0.symm) hπ k)
  have hS : v (∑ k ∈ Finset.range l, (1 + π) ^ k) = 1 := by
    rw [eS, AddValuation.map_add_eq_of_lt_left v hB, hvl]
  have e1 : (1 + π) ^ l - 1 = π * (∑ k ∈ Finset.range l, (1 + π) ^ k) := by
    have := geom_sum_mul (1 + π) l
    rw [add_sub_cancel_left] at this
    rw [← this, mul_comm]
  rw [e1, AddValuation.map_mul, hπ, hS]

theorem pow_lk_val (l : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (hvl : v (l : LL) = 1) {y : LL}
    {a : WithTop ℚ} (ha : 1 ≤ a) (h : v (y - 1) = a) (k : ℕ) :
    v (y ^ (l ^ k) - 1) = a + k := by
  induction k with
  | zero => rw [pow_zero, pow_one, h, Nat.cast_zero, add_zero]
  | succ k ih =>
    have hk0 : (0 : WithTop ℚ) ≤ k := by exact_mod_cast (Nat.cast_nonneg k : (0 : ℚ) ≤ k)
    rw [pow_succ, pow_mul, pow_l_val v l hl hl2 hvl (le_trans ha (le_add_of_nonneg_right hk0)) ih,
      Nat.cast_succ, add_assoc]

theorem chi_pow_nat_val (l : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (hvl : v (l : LL) = 1) (χ : LL)
    (hχ : v (χ - 1) = 1) (n : ℕ) (hn : n ≠ 0) :
    v (χ ^ n - 1) = ((1 + padicValNat l n : ℕ) : WithTop ℚ) := by
  obtain ⟨k, r, hr, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.ne_one
  have hr0 : r ≠ 0 := by rintro rfl; simp at hn
  have hcop : Nat.Coprime r l := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hr).symm
  have : Fact l.Prime := ⟨hl⟩
  have hpv : padicValNat l (l ^ k * r) = k := by
    rw [padicValNat.mul (pow_ne_zero k hl.ne_zero) hr0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hr, add_zero]
  have hk0 : (0 : WithTop ℚ) ≤ k := by exact_mod_cast (Nat.cast_nonneg k : (0 : ℚ) ≤ k)
  have hlk := pow_lk_val v l hl hl2 hvl (le_refl 1) hχ k
  rw [hpv, pow_mul, pow_coprime_val v l hvl
    (lt_of_lt_of_le zero_lt_one' (le_add_of_nonneg_right hk0)) hlk r hcop]
  push_cast
  rfl

theorem zpow_val_zero {x : LL} (hx : v x = 0) (hne : x ≠ 0) (z : ℤ) : v (x ^ z) = 0 := by
  have hn : ∀ n : ℕ, v (x ^ n) = 0 := fun n => by rw [AddValuation.map_pow, hx, smul_zero]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [zpow_natCast]; exact hn n
  · rw [zpow_neg, zpow_natCast]
    have h1 : v ((x ^ n)⁻¹ * x ^ n) = 0 := by
      rw [inv_mul_cancel₀ (pow_ne_zero n hne), AddValuation.map_one]
    rwa [AddValuation.map_mul, hn n, add_zero] at h1

theorem ne_zero_of_val_zero {x : LL} (hx : v x = 0) : x ≠ 0 := by
  rintro rfl
  rw [AddValuation.map_zero] at hx
  simp at hx

end LemGA

theorem chi_pow_val {LL : Type*} [Field LL] (v : AddValuation LL (WithTop ℚ)) (l : ℕ) [Fact l.Prime]
    (hl2 : l ≠ 2) (hvl : v (l : LL) = 1) (χ : LL) (hχ : v (χ - 1) = 1) (m : ℤ) (hm : m ≠ 0) :
    v (χ ^ m - 1) = ((1 + padicValInt l m : ℕ) : WithTop ℚ) := by
  have hl : l.Prime := Fact.out
  have hχ0 : v χ = 0 := LemGA.val_eq_zero_of_sub_one v (by rw [hχ]; exact LemGA.zero_lt_one')
  have hne : χ ≠ 0 := LemGA.ne_zero_of_val_zero v hχ0
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have hn : n ≠ 0 := by rintro rfl; exact hm rfl
    rw [zpow_natCast, padicValInt.of_nat]
    exact LemGA.chi_pow_nat_val v l hl hl2 hvl χ hχ n hn
  · have hn : n ≠ 0 := by rintro rfl; exact hm (by simp)
    have hpv : padicValInt l (-(n : ℤ)) = padicValNat l n := by
      unfold padicValInt; rw [Int.natAbs_neg]; simp
    rw [hpv, zpow_neg, zpow_natCast]
    have hxn : v (χ ^ n) = 0 := by
      rw [AddValuation.map_pow, hχ0, smul_zero]
    have hinv : v ((χ ^ n)⁻¹) = 0 := by
      have := LemGA.zpow_val_zero v hχ0 hne (-(n : ℤ))
      rwa [zpow_neg, zpow_natCast] at this
    have e : (χ ^ n)⁻¹ - 1 = (χ ^ n)⁻¹ * -(χ ^ n - 1) := by
      rw [mul_neg, mul_sub, inv_mul_cancel₀ (pow_ne_zero n hne), mul_one]; ring
    rw [e, AddValuation.map_mul, AddValuation.map_neg, hinv, zero_add]
    exact LemGA.chi_pow_nat_val v l hl hl2 hvl χ hχ n hn

theorem cc_assoc {LL O : Type*} [Field LL] [CommRing O] [Algebra O LL] (v : AddValuation LL (WithTop ℚ))
    (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2) (hvl : v (l : LL) = 1)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (u : Oˣ) (hu : v (algebraMap O LL (u : O) - 1) = 1)
    (cc : ℤ → O) (hcc : ∀ m : ℤ, (-(l : O)) * cc m = ((u ^ (-m) : Oˣ) : O) - 1) :
    ∀ j j' : ℤ, j ≠ j' → Associated (cc j - cc j') ((l : O) ^ padicValInt l (j - j')) := by
  intro j j' hjj
  obtain ⟨χ, hχdef⟩ : ∃ χ, χ = algebraMap O LL (u : O) := ⟨_, rfl⟩
  rw [← hχdef] at hu
  have hχ0 : v χ = 0 := LemGA.val_eq_zero_of_sub_one v (by rw [hu]; exact LemGA.zero_lt_one')
  have hne : χ ≠ 0 := LemGA.ne_zero_of_val_zero v hχ0
  have hmap : ∀ m : ℤ, algebraMap O LL ((u ^ m : Oˣ) : O) = χ ^ m := by
    intro m
    have h1 := Units.coe_map (algebraMap O LL).toMonoidHom (u ^ m)
    rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map] at h1
    rw [hχdef]
    exact h1.symm
  have hX : -(l : LL) * algebraMap O LL (cc j - cc j') = χ ^ (-j) - χ ^ (-j') := by
    have a1 := congrArg (algebraMap O LL) (hcc j)
    have a2 := congrArg (algebraMap O LL) (hcc j')
    rw [map_mul, map_neg, map_natCast, map_sub, map_one, hmap] at a1 a2
    rw [map_sub, mul_sub, a1, a2]; ring
  have hR : χ ^ (-j) - χ ^ (-j') = χ ^ (-j') * (χ ^ (j' - j) - 1) := by
    rw [mul_sub, mul_one, ← zpow_add₀ hne, show -j' + (j' - j) = -j by ring]
  have hpv : padicValInt l (j' - j) = padicValInt l (j - j') := by
    unfold padicValInt; rw [← Int.natAbs_neg, neg_sub]
  set k := padicValInt l (j - j') with hkdef
  have hjj' : j' - j ≠ 0 := sub_ne_zero.mpr (Ne.symm hjj)
  have hvX : v (algebraMap O LL (cc j - cc j')) = (k : WithTop ℚ) := by
    have h1 := congrArg v hX
    rw [hR, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_neg, hvl,
      LemGA.zpow_val_zero v hχ0 hne, zero_add, chi_pow_val v l hl2 hvl χ hu (j' - j) hjj', hpv,
      Nat.cast_add, Nat.cast_one] at h1
    exact WithTop.add_left_cancel WithTop.one_ne_top h1
  obtain ⟨XL, hXL⟩ : ∃ XL, XL = algebraMap O LL (cc j - cc j') := ⟨_, rfl⟩
  rw [← hXL] at hvX
  have hYL : algebraMap O LL ((l : O) ^ k) = (l : LL) ^ k := by rw [map_pow, map_natCast]
  have hvY : v ((l : LL) ^ k) = (k : WithTop ℚ) := by rw [AddValuation.map_pow, hvl, nsmul_one]
  have hXne : XL ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hvX; exact WithTop.natCast_ne_top k hvX.symm
  have hYne : (l : LL) ^ k ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hvY; exact WithTop.natCast_ne_top k hvY.symm
  have hq1 : v ((l : LL) ^ k / XL) = 0 := by
    have h1 : v ((l : LL) ^ k / XL * XL) = v ((l : LL) ^ k) := by rw [div_mul_cancel₀ _ hXne]
    rw [AddValuation.map_mul, hvX, hvY] at h1
    exact WithTop.add_right_cancel (WithTop.natCast_ne_top k) (h1.trans (zero_add _).symm)
  have hq2 : v (XL / (l : LL) ^ k) = 0 := by
    have h1 : v (XL / (l : LL) ^ k * (l : LL) ^ k) = v XL := by rw [div_mul_cancel₀ _ hYne]
    rw [AddValuation.map_mul, hvX, hvY] at h1
    exact WithTop.add_right_cancel (WithTop.natCast_ne_top k) (h1.trans (zero_add _).symm)
  obtain ⟨w0, hw0⟩ := hOv _ (le_of_eq hq1.symm)
  obtain ⟨w1, hw1⟩ := hOv _ (le_of_eq hq2.symm)
  have h01 : w0 * w1 = 1 := hinj (by
    rw [map_mul, hw0, hw1, map_one, div_mul_div_comm, mul_comm, div_self (mul_ne_zero hXne hYne)])
  refine ⟨⟨w0, w1, h01, by rw [mul_comm]; exact h01⟩, ?_⟩
  apply hinj
  show algebraMap O LL ((cc j - cc j') * w0) = algebraMap O LL ((l : O) ^ k)
  rw [map_mul, ← hXL, hw0, hYL, mul_div_cancel₀ _ hXne]

end Formalism.MainNotions.N.FrobeniusPowerSeries

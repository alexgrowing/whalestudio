import Mathlib

namespace FunctorialResolution.EmbeddedResolution

open IsLocalRing

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

noncomputable def idealOrder (I : Ideal R) : ℕ∞ :=
  sSup ((fun n : ℕ => (n : ℕ∞)) '' {n : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ n})

theorem le_idealOrder_iff (I : Ideal R) (n : ℕ) :
    (n : ℕ∞) ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R ^ n := by
  have hdef : idealOrder I
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  constructor
  · intro h
    by_contra hI
    rw [hdef] at h
    have hn : n ≠ 0 := by
      rintro rfl
      apply hI
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
    have hsup : sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k})
        ≤ ((n - 1 : ℕ) : ℕ∞) := by
      apply sSup_le
      rintro x ⟨k, hk, rfl⟩
      have hk' : I ≤ IsLocalRing.maximalIdeal R ^ k := hk
      have hkn : k < n := by
        by_contra hkn
        push Not at hkn
        exact hI (le_trans hk' (Ideal.pow_le_pow_right hkn))
      have hk2 : k ≤ n - 1 := by omega
      show (k : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞)
      exact_mod_cast hk2
    have hcon : n ≤ n - 1 := by exact_mod_cast h.trans hsup
    omega
  · intro h
    rw [hdef]
    exact le_sSup ⟨n, h, rfl⟩

theorem idealOrder_eq_top_iff (I : Ideal R) :
    idealOrder I = ⊤ ↔ ∀ n : ℕ, I ≤ IsLocalRing.maximalIdeal R ^ n := by
  constructor
  · intro h n
    rw [← le_idealOrder_iff, h]
    exact le_top
  · intro h
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (le_idealOrder_iff I n).mpr (h n)

theorem one_le_idealOrder_iff (I : Ideal R) :
    1 ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R := by
  have h := le_idealOrder_iff I 1
  rw [Nat.cast_one, pow_one] at h
  exact h

theorem one_le_idealOrder_iff_ne_top (I : Ideal R) :
    1 ≤ idealOrder I ↔ I ≠ ⊤ := by
  rw [one_le_idealOrder_iff]
  constructor
  · intro h hI
    rw [hI] at h
    exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp h)
  · intro h
    exact IsLocalRing.le_maximalIdeal h

theorem idealOrder_eq_zero_iff (I : Ideal R) :
    idealOrder I = 0 ↔ ¬ I ≤ IsLocalRing.maximalIdeal R := by
  rw [← one_le_idealOrder_iff, not_le, Order.lt_one_iff]

theorem idealOrder_top : idealOrder (⊤ : Ideal R) = 0 := by
  by_contra h
  have h1 : (1 : ℕ∞) ≤ idealOrder (⊤ : Ideal R) := by
    rw [Order.one_le_iff_ne_zero]
    exact h
  rw [one_le_idealOrder_iff_ne_top] at h1
  exact h1 rfl

theorem idealOrder_bot : idealOrder (⊥ : Ideal R) = ⊤ := by
  rw [idealOrder_eq_top_iff]
  intro n
  exact bot_le

theorem idealOrder_ne_top_of_ne_bot [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊥) :
    idealOrder I ≠ ⊤ := by
  intro h
  rw [idealOrder_eq_top_iff] at h
  have key : (⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (I := IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hle : I ≤ ⊥ := by
    rw [← key]
    exact le_iInf h
  exact hI (le_bot_iff.mp hle)

theorem exists_idealOrder_eq_coe [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊥) :
    ∃ n : ℕ, idealOrder I = (n : ℕ∞) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (idealOrder_ne_top_of_ne_bot hI)
  exact ⟨n, hn.symm⟩

theorem idealOrder_le_of_le {I J : Ideal R} (h : I ≤ J) : idealOrder J ≤ idealOrder I := by
  have hI : idealOrder I
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  have hJ : idealOrder J
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | J ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  rw [hI, hJ]
  apply sSup_le
  rintro x ⟨n, hn, rfl⟩
  have hn' : I ≤ IsLocalRing.maximalIdeal R ^ n := le_trans h hn
  exact le_sSup ⟨n, hn', rfl⟩

theorem idealOrder_sup (I J : Ideal R) :
    idealOrder (I ⊔ J) = min (idealOrder I) (idealOrder J) := by
  apply le_antisymm
  · exact le_min (idealOrder_le_of_le (le_sup_left : I ≤ I ⊔ J))
      (idealOrder_le_of_le (le_sup_right : J ≤ I ⊔ J))
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    rw [le_min_iff] at hn
    rw [le_idealOrder_iff]
    exact sup_le ((le_idealOrder_iff I n).mp hn.1) ((le_idealOrder_iff J n).mp hn.2)

private theorem enat_add_le_of_forall_natCast_add_le {a b c : ℕ∞}
    (h : ∀ m n : ℕ, (m : ℕ∞) ≤ a → (n : ℕ∞) ≤ b → ((m + n : ℕ) : ℕ∞) ≤ c) : a + b ≤ c := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · have hc : c = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro n
      have hn := h n 0 le_top (by simp)
      simpa using hn
    rw [hc]
    exact le_top
  rcases eq_or_ne b ⊤ with rfl | hb
  · have hc : c = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro n
      have hn := h 0 n (by simp) le_top
      simpa using hn
    rw [hc]
    exact le_top
  lift a to ℕ using ha
  lift b to ℕ using hb
  have hab := h a b le_rfl le_rfl
  simpa using hab

theorem add_idealOrder_le_idealOrder_mul (I J : Ideal R) :
    idealOrder I + idealOrder J ≤ idealOrder (I * J) := by
  refine enat_add_le_of_forall_natCast_add_le (fun m n hm hn => ?_)
  rw [le_idealOrder_iff] at hm hn ⊢
  rw [pow_add]
  exact Ideal.mul_mono hm hn

theorem mul_idealOrder_le_idealOrder_pow (I : Ideal R) (c : ℕ) :
    (c : ℕ∞) * idealOrder I ≤ idealOrder (I ^ c) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.cast_zero, zero_mul]
    exact zero_le
  · have hc1 : 1 ≤ c := hc
    rcases eq_or_ne (idealOrder I) ⊤ with hI | hI
    · have hIall : ∀ n : ℕ, I ≤ IsLocalRing.maximalIdeal R ^ n :=
        (idealOrder_eq_top_iff I).mp hI
      have htop : idealOrder (I ^ c) = ⊤ := by
        rw [idealOrder_eq_top_iff]
        intro n
        have h1 : I ^ c ≤ I ^ 1 := Ideal.pow_le_pow_right hc1
        rw [pow_one] at h1
        exact le_trans h1 (hIall n)
      rw [htop]
      exact le_top
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hI
      have hIk : I ≤ IsLocalRing.maximalIdeal R ^ k := (le_idealOrder_iff I k).mp hk.le
      rw [← hk, ← Nat.cast_mul, le_idealOrder_iff]
      calc I ^ c ≤ (IsLocalRing.maximalIdeal R ^ k) ^ c :=
            Ideal.pow_right_mono hIk c
        _ = IsLocalRing.maximalIdeal R ^ (c * k) := by rw [← pow_mul, mul_comm k c]

private theorem map_maximalIdeal_pow_le_pow (f : R →+* S)
    (hf : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S) (n : ℕ) :
    ((IsLocalRing.maximalIdeal R) ^ n).map f ≤ (IsLocalRing.maximalIdeal S) ^ n := by
  induction n with
  | zero =>
      have hS : (IsLocalRing.maximalIdeal S) ^ 0 = (⊤ : Ideal S) := by
        rw [pow_zero, Ideal.one_eq_top]
      rw [hS]
      exact le_top
  | succ n ih =>
      rw [pow_succ, pow_succ, Ideal.map_mul]
      exact Ideal.mul_mono ih hf

theorem idealOrder_le_idealOrder_map (f : R →+* S)
    (hf : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S) (I : Ideal R) :
    idealOrder I ≤ idealOrder (I.map f) := by
  refine ENat.forall_natCast_le_iff_le.mp (fun n hn => ?_)
  rw [le_idealOrder_iff] at hn ⊢
  exact le_trans (Ideal.map_mono hn) (map_maximalIdeal_pow_le_pow f hf n)

end FunctorialResolution.EmbeddedResolution

import Mathlib

open IsDedekindDomain WithZero

namespace GlobalTheory

theorem exists_span_eq_pow_card_classGroup {A : Type} [CommRing A] [IsDedekindDomain A]
    [Finite (ClassGroup A)] (P : Ideal A) (hP : P ≠ ⊥) :
    ∃ x : A, P ^ Nat.card (ClassGroup A) = Ideal.span {x} := by
  have hm : P ∈ nonZeroDivisors (Ideal A) := mem_nonZeroDivisors_of_ne_zero hP
  have hm' : P ^ Nat.card (ClassGroup A) ∈ nonZeroDivisors (Ideal A) := pow_mem hm _
  have h1 : ClassGroup.mk0 (⟨_, hm'⟩ : nonZeroDivisors (Ideal A)) = 1 := by
    have : (⟨_, hm'⟩ : nonZeroDivisors (Ideal A)) =
        (⟨P, hm⟩ : nonZeroDivisors (Ideal A)) ^ Nat.card (ClassGroup A) := Subtype.ext rfl
    rw [this, map_pow]; exact pow_card_eq_one'
  obtain ⟨x, hx⟩ := ((ClassGroup.mk0_eq_one_iff hm').1 h1).principal
  exact ⟨x, hx⟩

theorem ne_zero_of_pow_eq_span {A : Type} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) (hP : P ≠ ⊥) (k : ℕ) (x : A) (hx : P ^ k = Ideal.span {x}) : x ≠ 0 := by
  have : P ^ k ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]; exact pow_ne_zero _ (by rwa [Ideal.zero_eq_bot])
  rwa [hx, Ne, Ideal.span_singleton_eq_bot] at this

theorem intValuation_of_pow_eq_span {A : Type} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) (P : Ideal A) [hPp : P.IsPrime] (hP : P ≠ ⊥) (k : ℕ) (x : A)
    (hx : P ^ k = Ideal.span {x}) :
    v.intValuation x = if v.asIdeal = P then exp (-(k : ℤ)) else 1 := by
  have hx0 := ne_zero_of_pow_eq_span P hP k x hx
  rw [v.intValuation_eq_exp_neg_multiplicity hx0, ← hx]
  split_ifs with h
  · subst h
    rw [multiplicity_pow_self_of_prime v.prime]
  · have : multiplicity v.asIdeal (P ^ k) = 0 := by
      rw [multiplicity_eq_zero]
      intro hd
      have hle : P ^ k ≤ v.asIdeal := Ideal.le_of_dvd hd
      have hPv : P ≤ v.asIdeal := v.isPrime.le_of_pow_le hle
      exact h ((hPp.isMaximal hP).eq_of_le v.isPrime.ne_top hPv).symm
    rw [this]; simp

theorem mem_pow_of_intValuation_eq {A : Type} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) (x : A) (k : ℕ) (h : v.intValuation x = exp (-(k : ℤ))) :
    x ∈ v.asIdeal ^ k ∧ x ∉ v.asIdeal ^ (k + 1) := by
  refine ⟨(v.intValuation_le_pow_iff_mem x k).1 h.le, fun hm => ?_⟩
  have := (v.intValuation_le_pow_iff_mem x (k + 1)).2 hm
  rw [h, exp_le_exp] at this
  push_cast at this; omega

theorem exists_num_den_of_rat_divisor : ∀ (A : Type) [CommRing A] [IsDedekindDomain A] [Finite (ClassGroup A)] (S : Finset (Ideal A))
    (q : Ideal A → ℚ), ∃ (m : ℕ) (a b : A), 0 < m ∧ a ≠ 0 ∧ b ≠ 0 ∧ ∀ P : Ideal A, P.IsPrime → P ≠ ⊥ →
      ∃ na nb : ℕ, a ∈ P ^ na ∧ a ∉ P ^ (na + 1) ∧ b ∈ P ^ nb ∧ b ∉ P ^ (nb + 1) ∧
        ((na : ℚ) - nb = (m : ℚ) * (if P ∈ S then q P else 0)) := by
  intro A _ _ _ S q
  classical
  set h := Nat.card (ClassGroup A) with hh
  have hpos : 0 < h := Nat.card_pos
  set d : ℕ := ∏ P ∈ S, (q P).den with hd
  have dpos : 0 < d := Finset.prod_pos fun P _ => (q P).den_pos
  have hint : ∀ P, ∃ z : ℤ, P ∈ S → (d : ℚ) * q P = z := by
    intro P
    by_cases hP : P ∈ S
    · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun P => (q P).den) hP
      refine ⟨(k : ℤ) * (q P).num, fun _ => ?_⟩
      have hk' : (d : ℚ) = (q P).den * k := by exact_mod_cast hk
      have e := Rat.mul_den_eq_num (q P)
      rw [hk']; push_cast; rw [← e]; ring
    · exact ⟨0, fun h' => absurd h' hP⟩
  choose n hn using hint
  have hgen : ∀ P : Ideal A, ∃ x : A, P ≠ ⊥ → P ^ h = Ideal.span {x} := by
    intro P
    by_cases hP : P = ⊥
    · exact ⟨0, fun h' => absurd hP h'⟩
    · obtain ⟨x, hx⟩ := exists_span_eq_pow_card_classGroup P hP
      exact ⟨x, fun _ => hx⟩
  choose g hg using hgen
  set S' := S.filter (fun P => P.IsPrime ∧ P ≠ ⊥) with hS'
  have hval : ∀ (v : HeightOneSpectrum A) (e : Ideal A → ℕ),
      v.intValuation (∏ P ∈ S', g P ^ e P) =
        if v.asIdeal ∈ S' then exp (-((h * e v.asIdeal : ℕ) : ℤ)) else 1 := by
    intro v e
    rw [map_prod]
    have : ∀ P ∈ S', v.intValuation (g P ^ e P) =
        if v.asIdeal = P then exp (-((h * e v.asIdeal : ℕ) : ℤ)) else 1 := by
      intro P hP
      obtain ⟨_, hP1, hP2⟩ := Finset.mem_filter.1 hP
      haveI := hP1
      rw [map_pow, intValuation_of_pow_eq_span v P hP2 h (g P) (hg P hP2)]
      split_ifs with hv
      · subst hv; rw [← exp_nsmul]; congr 1; push_cast; ring
      · simp
    rw [Finset.prod_congr rfl this, Finset.prod_ite_eq]
  have hne : ∀ e : Ideal A → ℕ, (∏ P ∈ S', g P ^ e P) ≠ 0 := by
    intro e
    refine Finset.prod_ne_zero_iff.2 fun P hP => pow_ne_zero _ ?_
    obtain ⟨_, _, hP2⟩ := Finset.mem_filter.1 hP
    exact ne_zero_of_pow_eq_span P hP2 h (g P) (hg P hP2)
  refine ⟨d * h, ∏ P ∈ S', g P ^ (n P).toNat, ∏ P ∈ S', g P ^ (-n P).toNat,
    Nat.mul_pos dpos hpos, hne _, hne _, ?_⟩
  intro P hP hPb
  let v : HeightOneSpectrum A := ⟨P, hP, hPb⟩
  by_cases hS : P ∈ S
  · have hS'm : P ∈ S' := Finset.mem_filter.2 ⟨hS, hP, hPb⟩
    have ha := mem_pow_of_intValuation_eq v _ _ ((hval v (fun P => (n P).toNat)).trans (if_pos hS'm))
    have hb := mem_pow_of_intValuation_eq v _ _ ((hval v (fun P => (-n P).toNat)).trans (if_pos hS'm))
    refine ⟨h * (n P).toNat, h * (-n P).toNat, ha.1, ha.2, hb.1, hb.2, ?_⟩
    rw [if_pos hS]
    have key' : (((n P).toNat : ℕ) : ℚ) - (((-n P).toNat : ℕ) : ℚ) = (n P : ℚ) := by
      exact_mod_cast Int.toNat_sub_toNat_neg (n P)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ← mul_sub, key', ← hn P hS]
    ring
  · have hS'm : P ∉ S' := fun hm => hS (Finset.mem_filter.1 hm).1
    have h1 : ∀ e : Ideal A → ℕ, v.intValuation (∏ P ∈ S', g P ^ e P) = exp (-((0 : ℕ) : ℤ)) := by
      intro e
      rw [hval v e, if_neg hS'm]; simp
    have ha := mem_pow_of_intValuation_eq v _ _ (h1 (fun P => (n P).toNat))
    have hb := mem_pow_of_intValuation_eq v _ _ (h1 (fun P => (-n P).toNat))
    exact ⟨0, 0, ha.1, ha.2, hb.1, hb.2, by simp [hS]⟩

end GlobalTheory

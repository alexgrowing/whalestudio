import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ExistsPowDvdSubOfTwoPowDvdSubOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.TwoPowDvdSubOneOrAddOneOfPowTwoPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SumFilterTwoPowRootsEqZeroOfSumEqZero

open Finset

namespace UpperTheory.V.X

private theorem unit_of_odd (n : ℕ) (x : ℤ) (hx : Odd x) : IsUnit (x : ZMod (2 ^ n)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  push_cast
  apply IsCoprime.pow_left
  obtain ⟨t, rfl⟩ := hx
  exact ⟨-t, 1, by ring⟩

private theorem odd_of_unit (n : ℕ) (hn : 1 ≤ n) (u : ZMod (2 ^ n)) (hu : IsUnit u) : Odd (u.val : ℤ) := by
  have : IsUnit ((u.val : ℕ) : ZMod (2 ^ n)) := by simpa using hu
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_two_right] at this
  exact_mod_cast this

private theorem pm_of_pow {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (e m : ℕ) (he : 2 ≤ e)
    (ξ : ZMod (2 ^ (m + e)) →* k) (hz : ∀ u, ¬ IsUnit u → ξ u = 0) (hh : ξ (1 + 2 ^ (m + e - 1)) = -1)
    (u : ZMod (2 ^ (m + e))) (hu : ξ u ^ (2 ^ e) = 1) :
    (2 : ℤ) ^ m ∣ (u.val : ℤ) - 1 ∨ (2 : ℤ) ^ m ∣ (u.val : ℤ) + 1 := by
  apply UpperTheory.two_pow_dvd_sub_one_or_add_one_of_pow_two_pow e m
  have hU : IsUnit u := by
    by_contra h
    rw [hz u h, zero_pow (by positivity)] at hu
    exact zero_ne_one hu
  have hodd := odd_of_unit _ (by omega) u hU
  set x : ℤ := (u.val : ℤ) with hx
  by_contra hnd
  have hw0 : x ^ (2 ^ e) - 1 ≠ 0 := by
    intro h; rw [h] at hnd; exact hnd (dvd_zero _)
  have h4 : (2 : ℤ) ^ 2 ∣ x ^ (2 ^ e) - 1 := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ' 2 e', pow_mul]
    refine dvd_trans ?_ (sub_one_dvd_pow_sub_one (x ^ 2) (2 ^ e'))
    obtain ⟨t, ht⟩ := hodd
    exact ⟨t * t + t, by rw [ht]; ring⟩
  obtain ⟨j, b, hb, hjb⟩ := WfDvdMonoid.max_power_factor' hw0 (x := (2 : ℤ)) (by norm_num [Int.isUnit_iff])
  have hbo : Odd b := by rwa [← Int.not_even_iff_odd, even_iff_two_dvd]
  have hj2 : 2 ≤ j := by
    by_contra hlt
    rw [hjb] at h4
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl <;> omega
  have hjn : j ≤ m + e - 1 := by
    by_contra hlt
    apply hnd
    rw [hjb]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) b
  obtain ⟨i, hi⟩ := UpperTheory.exists_pow_dvd_sub_of_two_pow_dvd_sub_one (x ^ (2 ^ e)) b (1 + 2 ^ (m + e - 1)) j (m + e) hj2 hbo (by linear_combination hjb)
    (by simpa using pow_dvd_pow 2 hjn)
  have hi' : ((((x ^ (2 ^ e)) ^ i - (1 + 2 ^ (m + e - 1)) : ℤ)) : ZMod (2 ^ (m + e))) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hi
  push_cast at hi'
  have hxu : (x : ZMod (2 ^ (m + e))) = u := by simp [hx]
  rw [hxu, sub_eq_zero] at hi'
  have := congrArg ξ hi'
  rw [map_pow, map_pow, hu, one_pow, hh] at this
  apply h2
  linear_combination this

theorem lx_core {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (hl : l ≠ 2) (d e m s : ℕ) (a : ℤ) (he : 2 ≤ e) (ha : Odd a)
    (hQ : ((l ^ d : ℕ) : ℤ) = 1 + 2 ^ e * a) (hm : e ≤ m) (hs : s ≤ 2 ^ m) (hs1 : 1 < s) (hse : 2 ^ e ∣ s)
    (ξ : ZMod (2 ^ (m + e)) →* k) (hz : ∀ u, ¬ IsUnit u → ξ u = 0) (hh : ξ (1 + 2 ^ (m + e - 1)) = -1)
    (g : ZMod (2 ^ (m + e)) → k) (hg : ∀ u, g u ^ (l ^ d) = g u) (φ : ℕ → k) (c : k)
    (hd : ∀ u, g u - g (u - s) = c - if u.val < s then φ u.val else 0) (h1 : φ 1 = 1) (hodd : φ (s - 1) * ξ (-1) = -1) :
    ∑ u, ξ u * g u ≠ 0 := by
  classical
  intro h0
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have : (l : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff k l 2).1 (by exact_mod_cast h)
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have hzz : ∀ u, ξ u = 0 ∨ ξ u ^ (2 ^ (m + e)) = 1 := by
    intro u
    by_cases hu : IsUnit u
    · right
      obtain ⟨v, rfl⟩ := hu
      have hv : v ^ (2 ^ (m + e)) = 1 := by
        have h := ZMod.pow_totient v
        rw [Nat.totient_prime_pow Nat.prime_two (by omega)] at h
        have : 2 ^ (m + e) = 2 ^ (m + e - 1) * (2 - 1) * 2 := by
          rw [show 2 - 1 = 1 from rfl, mul_one, ← pow_succ]; congr 1; omega
        calc v ^ (2 ^ (m + e)) = v ^ (2 ^ (m + e - 1) * (2 - 1) * 2) := congrArg (fun t => v ^ t) this
          _ = 1 := by rw [pow_mul, h, one_pow]
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hv, Units.val_one, map_one]
    · exact Or.inl (hz u hu)
  have hE : ∀ y : ZMod (2 ^ (m + e)), IsUnit y →
      ∑ x ∈ univ.filter (fun x => ξ x ^ (2 ^ e) = 1), ξ x * g (x * y) = 0 := by
    intro y hy
    apply UpperTheory.sum_filter_two_pow_roots_eq_zero_of_sum_eq_zero k l hl d e (m + e) a he ha hQ _ ξ (fun x => g (x * y)) hzz (fun x => hg _)
    obtain ⟨v, rfl⟩ := hy
    have hv : ξ v ≠ 0 := ((Units.isUnit v).map ξ).ne_zero
    have := Equiv.sum_comp (Units.mulRight v) (fun u => ξ u * g u)
    rw [h0] at this
    apply mul_right_cancel₀ hv
    rw [Finset.sum_mul, zero_mul, ← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Units.mulRight_apply, map_mul]; ring
  have hy : IsUnit (1 - (s : ZMod (2 ^ (m + e)))) := by
    have := unit_of_odd (m + e) (1 - s) (by
      obtain ⟨t, rfl⟩ := hse
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      exact ⟨-(2 ^ e' * t), by push_cast; ring⟩)
    simpa using this
  let π : ZMod (2 ^ (m + e)) →+* ZMod (2 ^ m) := ZMod.castHom (pow_dvd_pow 2 (Nat.le_add_right m e)) _
  have hπ : ∀ x : ZMod (2 ^ (m + e)), π x = (x.val : ZMod (2 ^ m)) := by
    intro x; simp [π]
  have hlt : 2 ^ m < 2 ^ (m + e) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hm4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hker : ∀ x, π x = 0 → x * s = 0 := by
    intro x hx
    rw [hπ, ZMod.natCast_eq_zero_iff] at hx
    obtain ⟨p, hp⟩ := hx
    obtain ⟨t, rfl⟩ := hse
    rw [← ZMod.natCast_zmod_val x, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, hp]
    exact ⟨p * t, by ring⟩
  have hsmall : ∀ (x : ZMod (2 ^ (m + e))) (r : ℕ), r < 2 ^ m → x.val < 2 ^ m → π x = r → x.val = r := by
    intro x r hr hx h
    rw [hπ, ZMod.natCast_eq_natCast_iff] at h
    exact Nat.ModEq.eq_of_lt_of_lt h hx hr
  have hne : (-1 : ZMod (2 ^ m)) ≠ 1 := by
    intro h
    have : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by push_cast; linear_combination -h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hv1 : (1 : ZMod (2 ^ (m + e))).val = 1 := by
    rw [← Nat.cast_one, ZMod.val_natCast_of_lt (by omega)]
  have hvs : (-1 + s : ZMod (2 ^ (m + e))).val = s - 1 := by
    have : (-1 + s : ZMod (2 ^ (m + e))) = ((s - 1 : ℕ) : ZMod (2 ^ (m + e))) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, ZMod.val_natCast_of_lt (by omega)]
  have hT : ∀ x ∈ univ.filter (fun x => ξ x ^ (2 ^ e) = 1), ξ x * g (x * 1) - ξ x * g (x * (1 - s)) =
      (if π x = 1 then 1 else -1) * ξ x * c - (if x = 1 then 1 else 0) - (if x = -1 then 1 else 0) := by
    intro x hx
    rw [mem_filter] at hx
    by_cases hp : π x = 1
    · have hxs : x * (1 - s) = x - s := by
        have := hker (x - 1) (by rw [map_sub, hp, map_one, sub_self])
        linear_combination -this
      have hx' : x ≠ -1 := by
        rintro rfl
        rw [map_neg, map_one] at hp
        exact hne hp
      rw [mul_one, hxs, ← mul_sub, hd, if_pos hp, if_neg hx']
      by_cases hx1 : x = 1
      · subst hx1
        rw [hv1, if_pos hs1, if_pos rfl, h1, map_one]; ring
      · rw [if_neg hx1, if_neg]
        · ring
        · intro hlt'
          apply hx1
          have := hsmall x 1 (by omega) (by omega) (by simpa using hp)
          rw [← ZMod.natCast_zmod_val x, this, Nat.cast_one]
    · have hp' : π x = -1 := by
        rcases pm_of_pow h2 e m he ξ hz hh x hx.2 with h | h
        · exfalso; apply hp
          have : (((x.val : ℤ) - 1 : ℤ) : ZMod (2 ^ m)) = 0 := by
            rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
          rw [hπ]; rw [Int.cast_sub, Int.cast_natCast, Int.cast_one] at this; linear_combination this
        · have : (((x.val : ℤ) + 1 : ℤ) : ZMod (2 ^ m)) = 0 := by
            rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
          rw [hπ]; rw [Int.cast_add, Int.cast_natCast, Int.cast_one] at this; linear_combination this
      have hxs : x * (1 - s) = x + s := by
        have := hker (x + 1) (by rw [map_add, hp', map_one, neg_add_cancel])
        linear_combination -this
      have hx' : x ≠ 1 := by
        rintro rfl
        exact hp (map_one π)
      have hd' := hd (x + s)
      rw [add_sub_cancel_right] at hd'
      rw [mul_one, hxs, ← mul_sub, ← neg_sub, hd', if_neg hp, if_neg hx']
      by_cases hx1 : x = -1
      · subst hx1
        rw [hvs, if_pos (by omega), if_pos rfl]
        linear_combination hodd
      · rw [if_neg hx1, if_neg]
        · ring
        · intro hlt'
          apply hx1
          have := hsmall (x + s) (s - 1) (by omega) (by omega) (by
            rw [map_add, hp', map_natCast, Nat.cast_sub (by omega)]; push_cast; ring)
          rw [← hvs] at this
          exact add_right_cancel (ZMod.val_injective _ this)
  have hS := Finset.sum_congr rfl hT
  rw [Finset.sum_sub_distrib, hE _ isUnit_one, hE _ hy, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.sum_mul] at hS
  have hev : Even (2 ^ e) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hm1 : ξ (-1) ^ (2 ^ e) = 1 := by
    rw [← map_pow, hev.neg_one_pow, map_one]
  rw [if_pos (by simp), if_pos (by simp [hm1])] at hS
  have hx0 : IsUnit (1 + 2 ^ (m + e - 1) : ZMod (2 ^ (m + e))) := by
    by_contra h
    rw [hz _ h] at hh
    simp at hh
  have hπ0 : π (1 + 2 ^ (m + e - 1)) = 1 := by
    rw [map_add, map_one, map_pow, map_ofNat, add_eq_left]
    have : ((2 ^ (m + e - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact pow_dvd_pow 2 (by omega)
    exact_mod_cast this
  have hZ : ∑ x ∈ univ.filter (fun x => ξ x ^ (2 ^ e) = 1), (if π x = 1 then 1 else -1) * ξ x = 0 := by
    rw [Finset.sum_filter]
    obtain ⟨v, hv⟩ := hx0
    have := Equiv.sum_comp (Units.mulRight v) (fun x => if ξ x ^ (2 ^ e) = 1 then (if π x = 1 then 1 else -1) * ξ x else 0)
    simp only [Units.mulRight_apply, hv, map_mul, hh, hπ0, mul_one, mul_pow, hev.neg_one_pow] at this
    apply mul_left_cancel₀ h2
    rw [mul_zero, two_mul]
    nth_rewrite 1 [← this]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun x _ => ?_
    split_ifs <;> ring
  rw [hZ] at hS
  apply h2
  linear_combination hS

end UpperTheory.V.X

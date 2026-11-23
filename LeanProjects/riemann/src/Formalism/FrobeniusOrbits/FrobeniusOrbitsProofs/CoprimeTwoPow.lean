import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.TameInertiaTowers.TowerFieldFoundations

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Group

lemma coprime_two_pow (K : ℕ) {y : ℤ} (hy : Odd y) : IsCoprime ((2 : ℤ) ^ K) y := by
  obtain ⟨k, rfl⟩ := hy
  have h : IsCoprime (2 : ℤ) (2 * k + 1) := ⟨-k, 1, by ring⟩
  exact h.pow_left

lemma key (x : ℤ) (hx : Odd x) (K : ℕ) (hK : 1 ≤ K) :
    (2 : ℤ) ^ (K + 1) ∣ (x - 1) * (x + 1) ↔ (2 : ℤ) ^ K ∣ x - 1 ∨ (2 : ℤ) ^ K ∣ x + 1 := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨L, rfl⟩ : ∃ L, K = L + 1 := ⟨K - 1, by omega⟩
  have e1 : (2 * m + 1 - 1) * (2 * m + 1 + 1) = 4 * (m * (m + 1)) := by ring
  have e2 : (2 : ℤ) ^ (L + 1 + 1) = 4 * 2 ^ L := by ring
  have e3 : 2 * m + 1 - 1 = 2 * m := by ring
  have e4 : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
  have e5 : (2 : ℤ) ^ (L + 1) = 2 * 2 ^ L := by ring
  rw [e1, e2, e3, e4, e5, mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0),
    mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0), mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)]
  constructor
  · intro h
    rcases Int.even_or_odd m with hm | hm
    · exact Or.inl ((coprime_two_pow L hm.add_one).dvd_of_dvd_mul_right h)
    · exact Or.inr ((coprime_two_pow L hm).dvd_of_dvd_mul_left h)
  · rintro (h | h)
    · exact h.mul_right _
    · exact h.mul_left _

lemma not_four_dvd (x : ℤ) (hx : Odd x) : ¬ (4 : ℤ) ∣ x ^ 2 + 1 := by
  obtain ⟨m, rfl⟩ := hx
  rintro ⟨c, hc⟩
  have e : (2 * m + 1) ^ 2 + 1 = 4 * (m ^ 2 + m) + 2 := by ring
  rw [e] at hc
  generalize m ^ 2 + m = s at hc
  omega

lemma ind (l : ℤ) (hl : Odd l) (M : ℕ) (hM : 1 ≤ M) (j : ℕ) :
    ((2 : ℤ) ^ (M + j) ∣ l ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (M + j) ∣ l ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ M ∣ l - 1 ∨ (2 : ℤ) ^ M ∣ l + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih]
    have hx : Odd (l ^ (2 ^ j)) := hl.pow
    have e : l ^ (2 ^ (j + 1)) = (l ^ (2 ^ j)) ^ 2 := by
      rw [show (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j, pow_mul]
    have hK : M + (j + 1) = M + j + 1 := by omega
    rw [e, hK]
    have h4 : ¬ (2 : ℤ) ^ (M + j + 1) ∣ (l ^ (2 ^ j)) ^ 2 + 1 := by
      intro h
      apply not_four_dvd _ hx
      refine dvd_trans ?_ h
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    rw [or_iff_left h4, ← key _ hx _ (by omega)]
    have e6 : (l ^ (2 ^ j)) ^ 2 - 1 = (l ^ (2 ^ j) - 1) * (l ^ (2 ^ j) + 1) := by ring
    rw [e6]

lemma cast_eq_one (m : ℕ) (z : ℤ) : (z : ZMod m) = 1 ↔ (m : ℤ) ∣ z - 1 := by
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub 1 z m
  rw [Int.cast_one] at h
  rw [← h]
  exact eq_comm

lemma cast_eq_neg_one (m : ℕ) (z : ℤ) : (z : ZMod m) = -1 ↔ (m : ℤ) ∣ z + 1 := by
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub (-1) z m
  rw [Int.cast_neg, Int.cast_one, sub_neg_eq_add] at h
  rw [← h]
  exact eq_comm

lemma card_H (e : ℕ) : Nat.card (HGrp e) = 2 ^ e := by
  have hc : Nat.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega), show e + 2 - 1 = e + 1 by omega]
    simp
  have ho : orderOf (-1 : (ZMod (2 ^ (e + 2)))ˣ) = 2 := by
    apply orderOf_eq_prime
    · exact neg_one_sq
    · intro h
      have h' : ((1 : ℤ) : ZMod (2 ^ (e + 2))) = -1 := by
        have h0 := congrArg Units.val h
        simp only [Units.val_neg, Units.val_one] at h0
        rw [Int.cast_one]
        exact h0.symm
      rw [cast_eq_neg_one] at h'
      have h5 := Int.le_of_dvd (by norm_num) h'
      push_cast at h5
      have h2 : (2 : ℤ) ^ (e + 2) = 4 * 2 ^ e := by ring
      have h3 : (0 : ℤ) < 2 ^ e := by positivity
      rw [h2] at h5
      generalize (2 : ℤ) ^ e = s at h3 h5
      omega
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
  rw [Nat.card_zpowers, ho, hc] at h
  unfold HGrp
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (h.symm.trans (pow_succ 2 e))

lemma order_le (e : ℕ) (x : HGrp e) (j : ℕ) : orderOf x ≤ 2 ^ j ↔ x ^ (2 ^ j) = 1 := by
  have hd : orderOf x ∣ 2 ^ e := by
    have h0 : orderOf x ∣ Nat.card (HGrp e) := by
      first
        | exact orderOf_dvd_natCard x
        | exact orderOf_dvd_card
    rwa [card_H] at h0
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    rw [hi] at h
    have hij : i ≤ j := by
      by_contra hc
      push_neg at hc
      have hlt : 2 ^ j < 2 ^ i := by
        first
          | exact Nat.pow_lt_pow_right (by norm_num) hc
          | exact pow_lt_pow_right₀ (by norm_num) hc
          | exact Nat.pow_lt_pow_of_lt (by norm_num) hc
      exact absurd h (not_le.mpr hlt)
    rw [← orderOf_dvd_iff_pow_eq_one, hi]
    exact Nat.pow_dvd_pow 2 hij
  · intro h
    exact Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one h)

lemma order_le_card (e : ℕ) (x : HGrp e) : orderOf x ≤ 2 ^ e := by
  have h0 : orderOf x ∣ Nat.card (HGrp e) := by
    first
      | exact orderOf_dvd_natCard x
      | exact orderOf_dvd_card
  rw [card_H] at h0
  exact Nat.le_of_dvd (by positivity) h0

lemma hcl_pow_eq_one (e : ℕ) (u : (ZMod (2 ^ (e + 2)))ˣ) (k : ℕ) :
    (hcl e u) ^ k = 1 ↔ u ^ k = 1 ∨ u ^ k = -1 := by
  unfold hcl
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    rcases Int.even_or_odd n with h | h
    · left
      rw [← hn, h.neg_one_zpow]
    · right
      rw [← hn, h.neg_one_zpow]
  · rintro (h | h)
    · exact ⟨0, by rw [zpow_zero, h]⟩
    · exact ⟨1, by rw [zpow_one, h]⟩

lemma odd_of_unit (e : ℕ) (l : ℤ) (u : (ZMod (2 ^ (e + 2)))ˣ)
    (hu : (u : ZMod (2 ^ (e + 2))) = (l : ZMod _)) : Odd l := by
  by_contra hl
  rw [Int.not_odd_iff_even] at hl
  obtain ⟨c, rfl⟩ := hl
  have h1 : ((c + c : ℤ) : ZMod (2 ^ (e + 2))) * ((u⁻¹ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 1 := by
    rw [← hu, Units.mul_inv]
  have h2 := congrArg (ZMod.castHom (dvd_pow_self 2 (by omega : e + 2 ≠ 0)) (ZMod 2)) h1
  rw [map_mul, map_one, map_intCast] at h2
  have h3 : ((c + c : ℤ) : ZMod 2) = 0 := by
    first
      | (rw [Int.cast_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul])
      | (rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨c, by push_cast; ring⟩)
  rw [h3, zero_mul] at h2
  exact zero_ne_one h2

end Group

open Formalism.FrobeniusOrbits.Group

theorem hostExample : HostExample :=
  ⟨by norm_num [HostHyp], fun e => layerExists (e + 2) 11 7⟩

private lemma orderOf_hcl_u5_eq_two_pow (e : ℕ) : orderOf (hcl e (u5 (e + 2))) = 2 ^ e := by
  have hd : orderOf (hcl e (u5 (e + 2))) ∣ 2 ^ e := by
    have h0 : orderOf (hcl e (u5 (e + 2))) ∣ Nat.card (HGrp e) := by
      first
      | exact orderOf_dvd_natCard _
      | exact orderOf_dvd_card
    rwa [card_H] at h0
  obtain ⟨i, hie, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rw [hi]
  rcases Nat.lt_or_ge i e with hlt | hge
  · exfalso
    obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
    have hle : orderOf (hcl (j + 1) (u5 (j + 1 + 2))) ≤ 2 ^ j := by
      rw [hi]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [order_le, hcl_pow_eq_one] at hle
    have hv : ((u5 (j + 1 + 2) : (ZMod (2 ^ (j + 1 + 2)))ˣ) : ZMod (2 ^ (j + 1 + 2))) =
        ((5 : ℤ) : ZMod (2 ^ (j + 1 + 2))) := by
      first
        | (unfold u5; rw [ZMod.coe_unitOfCoprime]; norm_num)
        | (unfold u5; simp)
    have h5 : Odd (5 : ℤ) := ⟨2, by norm_num⟩
    have e3 : 3 + j = j + 1 + 2 := by omega
    rcases hle with h | h
    · have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, hv, Units.val_one, ← Int.cast_pow, cast_eq_one] at h'
      push_cast at h'
      have h8 := (ind 5 h5 3 (by norm_num) j).1 (Or.inl (by rw [e3]; exact h'))
      first
        | norm_num at h8
        | omega
    · have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, hv, Units.val_neg, Units.val_one, ← Int.cast_pow, cast_eq_neg_one] at h'
      push_cast at h'
      have h8 := (ind 5 h5 3 (by norm_num) j).1 (Or.inr (by rw [e3]; exact h'))
      first
        | norm_num at h8
        | omega
  · rw [show i = e by omega]

theorem hostGroup : HostGroup := by
  unfold HostGroup
  intro e
  have hne : (-1 : ℤˣ) ≠ 1 := by
    first
      | decide
      | (intro h; have h' := congrArg Units.val h; norm_num at h')
  have hU : Nat.card ℤˣ = 2 := by
    first
      | (rw [Nat.card_eq_fintype_card]; rfl)
      | (rw [Nat.card_eq_fintype_card]; decide)
      | simp
  have hfin : Finite (HGrp e) := Nat.finite_of_card_ne_zero (by rw [card_H]; positivity)
  have h5 := orderOf_hcl_u5_eq_two_pow e
  unfold GG Psi cc sg chD G0 c0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, card_H e, h5, ?_⟩
  · rw [Nat.card_prod, Nat.card_prod, hU, card_H]
    ring
  · have hs : Function.Surjective ((MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.fst (ℤˣ × ℤˣ) (HGrp e))) :=
      fun b => ⟨((1, b), 1), rfl⟩
    first
      | (rw [Subgroup.index_ker, Set.range_eq_univ.2 hs, Nat.card_univ, hU])
      | (rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top, hU])
  · intro h
    rw [MonoidHom.mem_ker] at h
    exact hne h
  · rw [MonoidHom.mem_ker]
    rfl
  · apply orderOf_eq_prime
    · exact Prod.ext (Prod.ext (by simp [sq]) (by simp [sq])) (by simp [sq])
    · intro h
      exact hne (congrArg (fun x => x.1.1) h)
  · exact isCyclic_of_orderOf_eq_card _ (by rw [h5, card_H])
  · have hg : hcl e (u5 (e + 2)) ^ (2 ^ e) = 1 := by
      rw [← h5]
      exact pow_orderOf_eq_one _
    let f0 : ℤ →+ Additive (HGrp e) := zmultiplesHom (Additive (HGrp e)) (Additive.ofMul (hcl e (u5 (e + 2))))
    have hf0 : f0 ((2 ^ e : ℕ) : ℤ) = 0 := by
      show ((2 ^ e : ℕ) : ℤ) • Additive.ofMul (hcl e (u5 (e + 2))) = 0
      first
        | (rw [← ofMul_zpow, zpow_natCast, hg, ofMul_one])
        | (rw [natCast_zsmul, ← ofMul_pow, hg, ofMul_one])
        | simp [← ofMul_zpow, hg]
    let f1 : ZMod (2 ^ e) →+ Additive (HGrp e) := ZMod.lift (2 ^ e) ⟨f0, hf0⟩
    let f : Multiplicative (ZMod (2 ^ e)) →* HGrp e :=
      { toFun := fun x => Additive.toMul (f1 (Multiplicative.toAdd x))
        map_one' := by
          first
            | simp
            | rfl
        map_mul' := fun x y => by
          first
            | simp
            | (rw [toAdd_mul, map_add, toMul_add]) }
    have hf1 : f (Multiplicative.ofAdd 1) = hcl e (u5 (e + 2)) := by
      show Additive.toMul (f1 1) = hcl e (u5 (e + 2))
      have h1 : (1 : ZMod (2 ^ e)) = ((1 : ℤ) : ZMod (2 ^ e)) := by simp
      rw [h1, ZMod.lift_coe]
      show Additive.toMul ((1 : ℤ) • Additive.ofMul (hcl e (u5 (e + 2)))) = hcl e (u5 (e + 2))
      rw [one_zsmul]
      rfl
    have hsurj : Function.Surjective f := by
      intro y
      have htop : Subgroup.zpowers (hcl e (u5 (e + 2))) = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, h5, card_H])
      have hy : y ∈ Subgroup.zpowers (hcl e (u5 (e + 2))) := by
        rw [htop]
        exact Subgroup.mem_top y
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine ⟨Multiplicative.ofAdd (k : ZMod (2 ^ e)), ?_⟩
      show Additive.toMul (f1 (k : ZMod (2 ^ e))) = y
      rw [ZMod.lift_coe]
      show Additive.toMul (k • Additive.ofMul (hcl e (u5 (e + 2)))) = y
      rw [← hk]
      first
        | rfl
        | simp [← ofMul_zpow]
    have hbij : Function.Bijective f := by
      haveI : NeZero (2 ^ e) := ⟨by positivity⟩
      have hc : Nat.card (Multiplicative (ZMod (2 ^ e))) ≤ Nat.card (HGrp e) := by
        change Nat.card (ZMod (2 ^ e)) ≤ Nat.card (HGrp e)
        rw [Nat.card_zmod, card_H]
      first
        | exact hsurj.bijective_of_nat_card_le hc
        | exact (Function.Surjective.bijective_of_nat_card_le hsurj hc)
    exact ⟨MulEquiv.ofBijective f hbij, hf1⟩

theorem hostOrders : HostOrders := by
  unfold HostOrders
  intro e
  refine ⟨fun j l u hu => ?_, ?_⟩
  · have hl : Odd l := odd_of_unit e l u hu
    have h1 : u ^ (2 ^ j) = 1 ↔ ((l ^ (2 ^ j) : ℤ) : ZMod (2 ^ (e + 2))) = 1 := by
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, hu, Units.val_one, Int.cast_pow]
    have h2 : u ^ (2 ^ j) = -1 ↔ ((l ^ (2 ^ j) : ℤ) : ZMod (2 ^ (e + 2))) = -1 := by
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, hu, Units.val_neg, Units.val_one, Int.cast_pow]
    rcases Nat.lt_or_ge (e + 1) j with hj | hj
    · simp only [cast_eq_one, cast_eq_neg_one]
      rw [show e + 2 - j = 0 by omega]
      simp only [pow_zero, Nat.cast_one, one_dvd, or_self, iff_true]
      exact (order_le_card e _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    · rw [order_le, hcl_pow_eq_one, h1, h2]
      simp only [cast_eq_one, cast_eq_neg_one]
      push_cast
      obtain ⟨M, hM⟩ : ∃ M, e + 2 = M + j := ⟨e + 2 - j, by omega⟩
      rw [hM, show M + j - j = M by omega]
      exact ind l hl M (by omega) j
  · unfold GG cc G0 c0
    have hne : (-1 : ℤˣ) ≠ 1 := by
      first
        | decide
        | (intro h; have h' := congrArg Units.val h; norm_num at h')
    intro g
    constructor
    · rw [Subgroup.mem_zpowers_iff]
      rintro ⟨k, hk⟩
      have hk1 : g.1.1 ^ k = -1 := congrArg (fun x => x.1.1) hk
      have hk2 : g.1.2 ^ k = -1 := congrArg (fun x => x.1.2) hk
      have hk3 : g.2 ^ k = 1 := congrArg (fun x => x.2) hk
      have hodd : Odd k := by
        rcases Int.even_or_odd k with he | ho
        · exfalso
          rcases Int.units_eq_one_or g.1.1 with h1 | h1
          · rw [h1, one_zpow] at hk1
            exact hne hk1.symm
          · rw [h1, he.neg_one_zpow] at hk1
            exact hne hk1.symm
        · exact ho
      have hu : ∀ v : ℤˣ, v ^ k = -1 → v = -1 := by
        intro v hv
        rcases Int.units_eq_one_or v with h1 | h1
        · rw [h1, one_zpow] at hv
          exact absurd hv.symm hne
        · exact h1
      have hg2 : g.2 = 1 := by
        have hd : (orderOf g.2 : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.2 hk3
        have hd2 : orderOf g.2 ∣ 2 ^ e := by
          have h0 : orderOf g.2 ∣ Nat.card (HGrp e) := by
            first
              | exact orderOf_dvd_natCard _
              | exact orderOf_dvd_card
          rwa [card_H] at h0
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
        have hi0 : i = 0 := by
          by_contra hne0
          obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          rw [hi, pow_succ] at hd
          push_cast at hd
          have h2k : (2 : ℤ) ∣ k := dvd_trans (Dvd.intro_left _ rfl) hd
          exact (Int.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2k)
        rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
        exact hi
      exact Prod.ext (Prod.ext (hu _ hk1) (hu _ hk2)) hg2
    · rintro rfl
      exact Subgroup.mem_zpowers _

theorem hostRecip : HostRecip := by
  unfold HostRecip
  intro q d h
  unfold HostHyp at h
  obtain ⟨-, -, hq8, hd16, hj⟩ := h
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  have hqo : Odd q := Nat.odd_iff.2 (by omega)
  have hdo : Odd d := Nat.odd_iff.2 (by omega)
  have hχq : ZMod.χ₄ (q : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four hq4
  have hχd : ZMod.χ₄ (d : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four hd4
  rw [jacobiSym.neg _ hqo, hχq] at hj
  rw [jacobiSym.neg _ hdo, hχd, jacobiSym.quadratic_reciprocity_three_mod_four hq4 hd4]
  linarith

end Formalism.FrobeniusOrbits

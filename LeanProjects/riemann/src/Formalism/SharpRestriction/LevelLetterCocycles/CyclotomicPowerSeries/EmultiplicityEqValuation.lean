import Mathlib

namespace LevelStatements.Ln03

open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem pow_dvd_iff_le_valuation (x : ℤ_[l]) (hx : x ≠ 0) (n : ℕ) :
    (l : ℤ_[l]) ^ n ∣ x ↔ n ≤ x.valuation := by
  first
  | (rw [← Ideal.mem_span_singleton]; exact PadicInt.mem_span_pow_iff_le_valuation x hx n)
  | (rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow];
     exact PadicInt.norm_le_pow_iff_le_valuation x hx n)

theorem emultiplicity_prime_eq_valuation (x : ℤ_[l]) (hx : x ≠ 0) :
    emultiplicity (l : ℤ_[l]) x = x.valuation := by
  rw [emultiplicity_eq_coe]
  refine ⟨(pow_dvd_iff_le_valuation x hx _).2 le_rfl, fun h => ?_⟩
  have := (pow_dvd_iff_le_valuation x hx _).1 h
  omega

theorem not_dvd_natCast (b : ℕ) (hb : ¬ l ∣ b) : ¬ (l : ℤ_[l]) ∣ (b : ℤ_[l]) := by
  intro h
  apply hb
  obtain ⟨c, hc⟩ := h
  have h2 := congrArg (PadicInt.toZMod : ℤ_[l] →+* ZMod l) hc
  simp only [map_natCast, map_mul, CharP.cast_eq_zero, ZMod.natCast_self, zero_mul] at h2
  exact (CharP.cast_eq_zero_iff (ZMod l) l b).1 h2

theorem toZModPow_eq_one_iff (k : ℕ) (x : ℤ_[l]) (hx : x - 1 ≠ 0) :
    PadicInt.toZModPow k x = 1 ↔ k ≤ (x - 1).valuation := by
  have h1 : PadicInt.toZModPow k x = 1 ↔ PadicInt.toZModPow k (x - 1) = 0 := by
    rw [map_sub, map_one, sub_eq_zero]
  rw [h1, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton,
    pow_dvd_iff_le_valuation _ hx]

private theorem prime_natCast_padicInt : Prime (l : ℤ_[l]) := by
  first
  | exact PadicInt.prime_p
  | exact UniqueFactorizationMonoid.irreducible_iff_prime.mp PadicInt.irreducible_p
  | exact PadicInt.irreducible_p.prime

theorem factV (hl2 : l ≠ 2) (u : ℤ_[l]) (hu : (u - 1).valuation = 1) (m : ℕ) (hm : m ≠ 0) :
    (u ^ m - 1).valuation = 1 + padicValNat l m := by
  have hl := (Fact.out : l.Prime)
  have hprime : Prime (l : ℤ_[l]) := prime_natCast_padicInt
  have hu0 : u - 1 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at hu
    omega
  have hdvd : (l : ℤ_[l]) ∣ u - 1 := by
    have := (pow_dvd_iff_le_valuation (u - 1) hu0 1).2 (by rw [hu])
    rwa [pow_one] at this
  have hndvd : ¬ (l : ℤ_[l]) ∣ u := by
    intro h
    have h1 : (l : ℤ_[l]) ∣ 1 := by
      have := dvd_sub h hdvd
      rwa [sub_sub_cancel] at this
    exact hprime.not_unit (isUnit_of_dvd_one h1)
  have hodd : Odd l := hl.odd_of_ne_two hl2
  obtain ⟨e, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm l hl.ne_one
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    exact hm' (dvd_zero l)
  have hval : padicValNat l (l ^ e * m') = e := by
    rw [padicValNat.mul (pow_ne_zero _ hl.ne_zero) hm'0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm', add_zero]
  rw [hval]
  have hE1 : emultiplicity (l : ℤ_[l]) (u ^ (l ^ e) - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + e := by
    have h : emultiplicity (l : ℤ_[l]) (u ^ (l ^ e) - 1 ^ (l ^ e)) =
        emultiplicity (l : ℤ_[l]) (u - 1) + e := by
      first
      | exact emultiplicity_pow_prime_pow_sub_pow_prime_pow hprime hodd hdvd hndvd e
      | exact multiplicity.emultiplicity_pow_prime_pow_sub_pow_prime_pow hprime hodd hdvd hndvd e
      | exact multiplicity.pow_prime_pow_sub_pow_prime_pow hprime hodd hdvd hndvd e
    rwa [one_pow] at h
  have hE2 : emultiplicity (l : ℤ_[l]) ((u ^ (l ^ e)) ^ m' - 1) =
      emultiplicity (l : ℤ_[l]) (u ^ (l ^ e) - 1) := by
    have hx1 : (l : ℤ_[l]) ∣ u ^ (l ^ e) - 1 := by
      have := sub_dvd_pow_sub_pow u 1 (l ^ e)
      rw [one_pow] at this
      exact hdvd.trans this
    have hx2 : ¬ (l : ℤ_[l]) ∣ u ^ (l ^ e) := fun h => hndvd (hprime.dvd_of_dvd_pow h)
    have hx3 : ¬ (l : ℤ_[l]) ∣ (m' : ℤ_[l]) := not_dvd_natCast m' hm'
    have h : emultiplicity (l : ℤ_[l]) ((u ^ (l ^ e)) ^ m' - 1 ^ m') =
        emultiplicity (l : ℤ_[l]) (u ^ (l ^ e) - 1) := by
      first
      | exact emultiplicity_pow_sub_pow_of_prime hprime hx1 hx2 hx3
      | exact multiplicity.emultiplicity_pow_sub_pow_of_prime hprime hx1 hx2 hx3
      | exact multiplicity.pow_sub_pow_of_prime hprime hx1 hx2 hx3
    rwa [one_pow] at h
  have htot : emultiplicity (l : ℤ_[l]) (u ^ (l ^ e * m') - 1) = ((1 + e : ℕ) : ℕ∞) := by
    rw [pow_mul, hE2, hE1, emultiplicity_prime_eq_valuation _ hu0, hu]
    first
    | norm_cast
    | simp
  have hne : u ^ (l ^ e * m') - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at htot
    first
    | exact ENat.top_ne_coe _ htot
    | simp at htot
  rw [emultiplicity_prime_eq_valuation _ hne] at htot
  exact_mod_cast htot

theorem orderOf_u (hl2 : l ≠ 2) (u : ℤ_[l]) (hu : (u - 1).valuation = 1) (s : ℕ) :
    orderOf (PadicInt.toZModPow (s + 1) u) = l ^ s := by
  have hl := (Fact.out : l.Prime)
  have key : ∀ j : ℕ, (PadicInt.toZModPow (s + 1) u) ^ (l ^ j) = 1 ↔ s ≤ j := by
    intro j
    have hv := factV hl2 u hu (l ^ j) (pow_ne_zero _ hl.ne_zero)
    rw [padicValNat.prime_pow] at hv
    have hne : u ^ (l ^ j) - 1 ≠ 0 := by
      intro h
      rw [h, PadicInt.valuation_zero] at hv
      omega
    rw [← map_pow, toZModPow_eq_one_iff _ _ hne, hv]
    omega
  cases s with
  | zero =>
    rw [pow_zero]
    exact orderOf_eq_one_iff.mpr ((pow_one _).symm.trans
      (by simpa only [pow_zero] using (key 0).2 le_rfl))
  | succ n =>
    apply orderOf_eq_prime_pow
    · rw [key]
      omega
    · exact (key (n + 1)).2 le_rfl

variable {LL : Type*} [Field LL] [CharZero LL]

theorem isPrimitiveRoot_pow_eq_pow_iff_zmod_eq {N : ℕ} [NeZero N] {ξ : LL} (hξ : IsPrimitiveRoot ξ N) (a b : ℕ) :
    ξ ^ a = ξ ^ b ↔ (a : ZMod N) = b := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hmod : ∀ c : ℕ, ξ ^ c = ξ ^ (c % N) := fun c => by
    conv_lhs => rw [← Nat.div_add_mod c N, pow_add, pow_mul, hξ.pow_eq_one, one_pow, one_mul]
  have hz : (a : ZMod N) = b ↔ a % N = b % N := by
    first
    | exact ZMod.natCast_eq_natCast_iff' a b N
    | (rw [ZMod.natCast_eq_natCast_iff]; rfl)
  rw [hz, hmod a, hmod b]
  exact ⟨fun h => hξ.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) h, fun h => by rw [h]⟩

theorem card_Rs {n : ℕ} {ζ : LL} (hζ : IsPrimitiveRoot ζ (l ^ n)) (s : ℕ) (hs : s < n) :
    (primitiveRoots (l ^ (s + 1)) LL).card = (l - 1) * l ^ s := by
  have hl := (Fact.out : l.Prime)
  have hpos : 0 < l ^ n := pow_pos hl.pos n
  have hprod : l ^ n = l ^ (n - (s + 1)) * l ^ (s + 1) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have h := hζ.pow hpos hprod
  rw [h.card_primitiveRoots, Nat.totient_prime_pow_succ hl, mul_comm]

private theorem mem_primitiveRoots_iff_isPrimitiveRoot {k : ℕ} (h0 : 0 < k) {ζ : LL} :
    ζ ∈ primitiveRoots k LL ↔ IsPrimitiveRoot ζ k := by
  first
  | exact mem_primitiveRoots h0
  | (haveI : NeZero k := ⟨h0.ne'⟩; exact mem_primitiveRoots)

theorem pow_mem_Rs (s : ℕ) (a : (ZMod (l ^ (s + 1)))ˣ) {ξ : LL}
    (hξ : ξ ∈ primitiveRoots (l ^ (s + 1)) LL) :
    ξ ^ (a : ZMod (l ^ (s + 1))).val ∈ primitiveRoots (l ^ (s + 1)) LL := by
  have h0 : 0 < l ^ (s + 1) := pow_pos (Fact.out : l.Prime).pos _
  rw [mem_primitiveRoots_iff_isPrimitiveRoot h0] at hξ ⊢
  exact hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)

theorem Rs_transitive (s : ℕ) {ξ η : LL} (hξ : ξ ∈ primitiveRoots (l ^ (s + 1)) LL)
    (hη : η ∈ primitiveRoots (l ^ (s + 1)) LL) :
    ∃! a : (ZMod (l ^ (s + 1)))ˣ, ξ ^ (a : ZMod (l ^ (s + 1))).val = η := by
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h0 : 0 < l ^ (s + 1) := pow_pos (Fact.out : l.Prime).pos _
  rw [mem_primitiveRoots_iff_isPrimitiveRoot h0] at hξ hη
  obtain ⟨i, -, hi⟩ : ∃ i < l ^ (s + 1), ξ ^ i = η := by
    first
    | exact hξ.eq_pow_of_pow_eq_one hη.pow_eq_one
    | exact hξ.eq_pow_of_pow_eq_one hη.pow_eq_one h0
  have hcop : i.Coprime (l ^ (s + 1)) := by
    first
    | exact (hξ.pow_iff_coprime h0 i).1 (hi ▸ hη)
    | exact (hξ.pow_iff_coprime i).1 (hi ▸ hη)
  refine ⟨ZMod.unitOfCoprime i hcop, ?_, ?_⟩
  · simp only [ZMod.coe_unitOfCoprime]
    rw [← hi, isPrimitiveRoot_pow_eq_pow_iff_zmod_eq hξ, ZMod.natCast_zmod_val]
  · intro b hb
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (b : ZMod (l ^ (s + 1))),
      ← isPrimitiveRoot_pow_eq_pow_iff_zmod_eq hξ]
    exact hb.trans hi.symm

private theorem isPrimitiveRoot_pow_val_mul_eq_pow_pow {N : ℕ} [NeZero N] {ξ : LL} (hξ : IsPrimitiveRoot ξ N)
    (x y : ZMod N) : ξ ^ (x * y).val = (ξ ^ x.val) ^ y.val := by
  rw [← pow_mul, isPrimitiveRoot_pow_eq_pow_iff_zmod_eq hξ, Nat.cast_mul]
  first
  | rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  | simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]

theorem invariants_const (hl2 : l ≠ 2) (s : ℕ) (u : ℤ_[l]) (hu : (u - 1).valuation = 1)
    (f : LL → LL)
    (hfu : ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
      f (ξ ^ (PadicInt.toZModPow (s + 1) u).val) = f ξ)
    (hfΔ : ∀ a : ZMod (l ^ (s + 1)), a ^ (l - 1) = 1 →
      ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL, f (ξ ^ a.val) = f ξ) :
    ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL, ∀ η ∈ primitiveRoots (l ^ (s + 1)) LL, f ξ = f η := by
  have hl := (Fact.out : l.Prime)
  have hl2le := hl.two_le
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h0 : 0 < l ^ (s + 1) := pow_pos hl.pos _
  have hmul : ∀ a b : (ZMod (l ^ (s + 1)))ˣ,
      (∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL, f (ξ ^ (a : ZMod (l ^ (s + 1))).val) = f ξ) →
      (∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL, f (ξ ^ (b : ZMod (l ^ (s + 1))).val) = f ξ) →
      ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
        f (ξ ^ ((a * b : (ZMod (l ^ (s + 1)))ˣ) : ZMod (l ^ (s + 1))).val) = f ξ := by
    intro a b ha hb ξ hξ
    have hξ' := (mem_primitiveRoots_iff_isPrimitiveRoot h0).1 hξ
    rw [Units.val_mul, isPrimitiveRoot_pow_val_mul_eq_pow_pow hξ',
      hb _ (pow_mem_Rs s a hξ), ha ξ hξ]
  have hord := orderOf_u hl2 u hu s
  have hxpow : (PadicInt.toZModPow (s + 1) u) ^ (l ^ s) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  obtain ⟨ub, hub⟩ : ∃ ub : (ZMod (l ^ (s + 1)))ˣ,
      (ub : ZMod (l ^ (s + 1))) = PadicInt.toZModPow (s + 1) u :=
    ⟨Units.ofPowEqOne _ (l ^ s) hxpow (pow_ne_zero _ hl.ne_zero), by
      first
      | exact Units.val_ofPowEqOne _ _ _ _
      | rfl⟩
  have hubord : orderOf ub = l ^ s := by
    rw [← orderOf_units, hub, hord]
  have hS_ub : ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
      f (ξ ^ (ub : ZMod (l ^ (s + 1))).val) = f ξ := by
    intro ξ hξ
    rw [hub]
    exact hfu ξ hξ
  have hpowS : ∀ k : ℕ, ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
      f (ξ ^ ((ub ^ k : (ZMod (l ^ (s + 1)))ˣ) : ZMod (l ^ (s + 1))).val) = f ξ := by
    intro k
    induction k with
    | zero =>
      intro ξ hξ
      rw [pow_zero, Units.val_one]
      exact hfΔ 1 (one_pow _) ξ hξ
    | succ n ih =>
      intro ξ hξ
      rw [pow_succ ub n]
      exact hmul _ _ ih hS_ub ξ hξ
  have hcopl : Nat.Coprime l (l - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hl]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hw : orderOf (ub ^ (l - 1)) = l ^ s := by
    have hcop : (orderOf ub).Coprime (l - 1) := by
      rw [hubord]
      exact Nat.Coprime.pow_left s hcopl
    first
    | rw [Nat.Coprime.orderOf_pow hcop, hubord]
    | rw [orderOf_pow_coprime hcop, hubord]
    | rw [orderOf_pow' ub (by omega : l - 1 ≠ 0), hcop.gcd_eq_one, Nat.div_one, hubord]
  haveI hcyc : IsCyclic (ZMod (l ^ (s + 1)))ˣ := by
    first
    | exact ZMod.isCyclic_units_of_prime_pow l hl hl2 (s + 1)
    | exact ZMod.isCyclic_units_of_prime_pow hl hl2 (s + 1)
    | exact ZMod.isCyclic_units_prime_pow l hl hl2 (s + 1)
  have hwpow : (ub ^ (l - 1)) ^ (l ^ s) = 1 := by
    rw [← hw]
    exact pow_orderOf_eq_one _
  have hcount : ∀ b : (ZMod (l ^ (s + 1)))ˣ, b ^ (l ^ s) = 1 → ∃ k : ℕ, (ub ^ (l - 1)) ^ k = b := by
    intro b hb
    have hsub : (Finset.range (l ^ s)).image (fun k => (ub ^ (l - 1)) ^ k) ⊆
        Finset.univ.filter (fun x : (ZMod (l ^ (s + 1)))ˣ => x ^ (l ^ s) = 1) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨k, -, rfl⟩ := hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [pow_right_comm (ub ^ (l - 1)) k (l ^ s), hwpow, one_pow]
    have hcard : ((Finset.range (l ^ s)).image (fun k => (ub ^ (l - 1)) ^ k)).card = l ^ s := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      have hi' : i < orderOf (ub ^ (l - 1)) := by
        rw [hw]
        simpa using hi
      have hj' : j < orderOf (ub ^ (l - 1)) := by
        rw [hw]
        simpa using hj
      first
      | exact pow_injOn_Iio_orderOf hi' hj' hij
      | (have h2 := (pow_inj_mod).1 hij
         rwa [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at h2)
    have hle := IsCyclic.card_pow_eq_one_le (α := (ZMod (l ^ (s + 1)))ˣ) (pow_pos hl.pos s)
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
    have hbmem : b ∈ Finset.univ.filter (fun x : (ZMod (l ^ (s + 1)))ˣ => x ^ (l ^ s) = 1) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hb⟩
    rw [← heq, Finset.mem_image] at hbmem
    obtain ⟨k, -, hk⟩ := hbmem
    exact ⟨k, hk⟩
  have hcardG : Fintype.card (ZMod (l ^ (s + 1)))ˣ = l ^ s * (l - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hl]
  have key : ∀ a : (ZMod (l ^ (s + 1)))ˣ, ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
      f (ξ ^ (a : ZMod (l ^ (s + 1))).val) = f ξ := by
    intro a
    obtain ⟨k, hk⟩ := hcount (a ^ (l - 1)) (by
      rw [← pow_mul, mul_comm, ← hcardG, pow_card_eq_one])
    have ht : ((ub ^ k)⁻¹ * a) ^ (l - 1) = 1 := by
      rw [mul_pow, inv_pow, ← hk, ← pow_mul, ← pow_mul, mul_comm k]
      first
      | exact inv_mul_cancel _
      | simp
    have hSt : ∀ ξ ∈ primitiveRoots (l ^ (s + 1)) LL,
        f (ξ ^ (((ub ^ k)⁻¹ * a : (ZMod (l ^ (s + 1)))ˣ) : ZMod (l ^ (s + 1))).val) = f ξ := by
      intro ξ hξ
      apply hfΔ _ _ ξ hξ
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    have ha : a = ub ^ k * ((ub ^ k)⁻¹ * a) := (mul_inv_cancel_left _ _).symm
    intro ξ hξ
    rw [ha]
    exact hmul _ _ (hpowS k) hSt ξ hξ
  intro ξ hξ η hη
  obtain ⟨a, ha, -⟩ := Rs_transitive s hξ hη
  have ha' : ξ ^ (a : ZMod (l ^ (s + 1))).val = η := ha
  rw [← ha', key a ξ hξ]

theorem sigma_u_order (hl2 : l ≠ 2) (s : ℕ) (u : ℤ_[l]) (hu : (u - 1).valuation = 1)
    {ξ : LL} (hξ : ξ ∈ primitiveRoots (l ^ (s + 1)) LL) (k : ℕ) :
    ξ ^ ((PadicInt.toZModPow (s + 1) u).val ^ k) = ξ ↔ l ^ s ∣ k := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h0 : 0 < l ^ (s + 1) := pow_pos hl.pos _
  rw [mem_primitiveRoots_iff_isPrimitiveRoot h0] at hξ
  have h := isPrimitiveRoot_pow_eq_pow_iff_zmod_eq hξ ((PadicInt.toZModPow (s + 1) u).val ^ k) 1
  rw [pow_one] at h
  rw [h, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, ← orderOf_dvd_iff_pow_eq_one,
    orderOf_u hl2 u hu s]

end LevelStatements.Ln03

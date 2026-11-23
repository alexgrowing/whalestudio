import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TateCoker

variable {l : ℕ} [hl : Fact l.Prime] {M N : Type} [CommGroup M] [CommGroup N] (φ : M →* N)

def lker (l : ℕ) : Subgroup M where
  carrier := {x | φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1}
  mul_mem' := by
    rintro a b ⟨ha, m, hm⟩ ⟨hb, m', hm'⟩
    refine ⟨by rw [map_mul, ha, hb, _root_.one_mul], m + m', ?_⟩
    rw [mul_pow, pow_add, pow_mul, hm, one_pow, mul_comm (l ^ m), pow_mul, hm', one_pow, _root_.one_mul]
  one_mem' := ⟨map_one φ, 0, one_pow _⟩
  inv_mem' := by
    rintro a ⟨ha, m, hm⟩
    exact ⟨by rw [map_inv, ha, inv_one], m, by rw [inv_pow, hm, inv_one]⟩

theorem pow_pow_eq_one {x : M} {m : ℕ} (h : x ^ l ^ m = 1) (j : ℕ) : x ^ l ^ (m + j) = 1 := by
  rw [pow_add, pow_mul, h, one_pow]

variable {φ}

theorem kill [Finite φ.ker] {k : M} (hk : φ k = 1) {m : ℕ} (hm : k ^ l ^ m = 1) :
    k ^ l ^ Nat.card φ.ker = 1 := by
  have hp : l.Prime := hl.out
  have h1 : orderOf k ∣ Nat.card φ.ker := Subgroup.orderOf_dvd_natCard _ hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hm)
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos_iff.2 ⟨⟨⟨1, map_one φ⟩⟩, inferInstance⟩
  have h2 : j ≤ Nat.card φ.ker :=
    ((Nat.lt_pow_self hp.one_lt).trans_le (Nat.le_of_dvd hpos (hj ▸ h1))).le
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ pow_dvd_pow l h2)

theorem exists_lift (hs : Function.Surjective φ) [Finite φ.ker] (n : ℕ) (y : N) (hy : y ^ l ^ n = 1) :
    ∃ x : M, φ x = y ∧ ∃ m : ℕ, x ^ l ^ m = 1 := by
  have hp : l.Prime := hl.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_one] at hy
    exact ⟨1, by rw [map_one, hy], 0, one_pow _⟩
  obtain ⟨x₀, rfl⟩ := hs y
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos_iff.2 ⟨⟨⟨1, map_one φ⟩⟩, inferInstance⟩
  have hk : x₀ ^ l ^ n ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hy]
  have hc : (x₀ ^ l ^ n) ^ Nat.card φ.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hk)
  obtain ⟨e, u, hu, hcu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' l hp.one_lt.ne'
  have hcop : Nat.Coprime u (l ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu))
  obtain ⟨w, -, hw⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Nat.one_lt_pow hn.ne' hp.one_lt)
  refine ⟨x₀ ^ (u * w), ?_, n + e, ?_⟩
  · rw [map_pow, pow_eq_pow_mod _ hy, hw, pow_one]
  · rw [← pow_mul, show u * w * l ^ (n + e) = l ^ n * Nat.card φ.ker * w by rw [hcu, pow_add]; ring,
      pow_mul, pow_mul, hc, one_pow]

theorem indep [Finite φ.ker] {x x' : M} (h : φ x = φ x') {m m' : ℕ} (hx : x ^ l ^ m = 1)
    (hx' : x' ^ l ^ m' = 1) : x ^ l ^ Nat.card φ.ker = x' ^ l ^ Nat.card φ.ker := by
  have h1 : φ (x * x'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : (x * x'⁻¹) ^ l ^ (m + m') = 1 := by
    rw [mul_pow, inv_pow, pow_pow_eq_one hx, add_comm, pow_pow_eq_one hx', inv_one, _root_.one_mul]
  have h3 := kill h1 h2
  rwa [mul_pow, inv_pow, mul_inv_eq_one] at h3

variable (hs : Function.Surjective φ) [Finite φ.ker]
include hs

def lift (t : Tate l N) (n : ℕ) : M := (exists_lift hs n (t.lev n) (t.lev_pow n)).choose

theorem lift_spec (t : Tate l N) (n : ℕ) : φ (lift hs t n) = t.lev n ∧ ∃ m : ℕ, lift hs t n ^ l ^ m = 1 :=
  (exists_lift hs n (t.lev n) (t.lev_pow n)).choose_spec

def del (t : Tate l N) : M := lift hs t (Nat.card φ.ker) ^ l ^ Nat.card φ.ker

theorem del_eq (t : Tate l N) {x : M} (hx : φ x = t.lev (Nat.card φ.ker)) {m : ℕ} (hm : x ^ l ^ m = 1) :
    del hs t = x ^ l ^ Nat.card φ.ker := by
  obtain ⟨h1, m', h2⟩ := lift_spec hs t (Nat.card φ.ker)
  exact indep (h1.trans hx.symm) h2 hm

theorem del_mem (t : Tate l N) : del hs t ∈ lker φ l := by
  obtain ⟨h1, m, h2⟩ := lift_spec hs t (Nat.card φ.ker)
  refine ⟨by rw [del, map_pow, h1, t.lev_pow], m, ?_⟩
  rw [del, ← pow_mul, mul_comm, pow_mul, h2, one_pow]

def delta : Tate l N →+ Additive (lker φ l) where
  toFun t := Additive.ofMul ⟨del hs t, del_mem hs t⟩
  map_zero' := by
    show Additive.ofMul _ = Additive.ofMul (1 : lker φ l)
    congr 1
    exact Subtype.ext ((del_eq hs 0 (x := 1) (m := 0) (by rw [map_one, Tate.lev_zero]) (one_pow _)).trans
      (one_pow _))
  map_add' s t := by
    show Additive.ofMul _ = Additive.ofMul (_ * _)
    congr 1
    apply Subtype.ext
    obtain ⟨hs1, m, hs2⟩ := lift_spec hs s (Nat.card φ.ker)
    obtain ⟨ht1, m', ht2⟩ := lift_spec hs t (Nat.card φ.ker)
    refine (del_eq hs (s + t) (x := lift hs s _ * lift hs t _) (m := m + m')
      (by rw [map_mul, hs1, ht1, Tate.lev_add]) ?_).trans ?_
    · rw [mul_pow, pow_pow_eq_one hs2, add_comm, pow_pow_eq_one ht2, _root_.one_mul]
    · rw [mul_pow]; rfl

theorem delta_surjective (hd : ∀ x : M, ∃ y, y ^ l = x) : Function.Surjective (delta (l := l) hs) := by
  intro k0
  set a := Nat.card φ.ker
  obtain ⟨⟨k, hk1, m, hm⟩, rfl⟩ : ∃ z : lker φ l, Additive.ofMul z = k0 := ⟨Additive.toMul k0, rfl⟩
  obtain ⟨s, hsa⟩ := GlobalTheory.Published.tate_lev_surj l M hd a k (kill hk1 hm)
  let t : Tate l N := Tate.mk (fun n => φ (s.lev (n + a))) fun n =>
    ⟨by rw [← map_pow, add_comm, s.lev_add_pow, hsa, hk1], by rw [← map_pow, add_right_comm, s.lev_succ]⟩
  refine ⟨t, ?_⟩
  show Additive.ofMul _ = Additive.ofMul _
  congr 1
  apply Subtype.ext
  exact (del_eq hs t (x := s.lev (a + a)) (m := a + a) rfl (s.lev_pow _)).trans
    ((s.lev_add_pow a a).trans hsa)

theorem delta_ker : (delta hs).ker = (LinearMap.range (Tate.map l φ)).toAddSubgroup := by
  set a := Nat.card φ.ker
  ext t
  have e0 : t ∈ (delta hs).ker ↔ del hs t = 1 := by
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro h; exact congrArg Subtype.val (congrArg Additive.toMul h)
    · intro h
      show Additive.ofMul _ = Additive.ofMul (1 : lker φ l)
      exact congrArg Additive.ofMul (Subtype.ext h)
  rw [e0, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  constructor
  · intro h
    have lv : ∀ n, (lift hs t (n + a) ^ l ^ n) ^ l ^ a = 1 := fun n => by
      obtain ⟨h1, m, h2⟩ := lift_spec hs t (n + a)
      rw [← h, del_eq hs t (x := lift hs t (n + a) ^ l ^ n) (m := m)
        (by rw [map_pow, h1, add_comm, t.lev_add_pow]) (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow])]
    let y : Tate l M := Tate.mk (fun n => lift hs t (n + a) ^ l ^ a) fun n => by
      refine ⟨by rw [← pow_mul, mul_comm, pow_mul]; exact lv n, ?_⟩
      obtain ⟨h1, m, h2⟩ := lift_spec hs t (n + 1 + a)
      obtain ⟨h1', m', h2'⟩ := lift_spec hs t (n + a)
      rw [← pow_mul, mul_comm, pow_mul]
      refine indep (m := m) (m' := m') ?_ (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow]) h2'
      rw [map_pow, h1, h1', show n + 1 + a = (n + a) + 1 by omega, t.lev_succ]
    refine ⟨y, Tate.ext fun n => ?_⟩
    rw [Tate.lev_map, Tate.lev_mk, map_pow, (lift_spec hs t (n + a)).1, t.lev_add_pow]
  · rintro ⟨y, rfl⟩
    exact (del_eq hs _ (x := y.lev a) (m := a) rfl (y.lev_pow a)).trans (y.lev_pow a)

omit hs in
theorem map_injective' : Function.Injective (Tate.map l φ) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => Tate.ext fun n => ?_
  have h1 : ∀ k, φ (y.lev k) = 1 := fun k => congrArg (·.lev k) hy
  rw [Tate.lev_zero, ← y.lev_add_pow n (Nat.card φ.ker)]
  exact kill (h1 _) (y.lev_pow _)

end GlobalTheory.TateCoker

namespace GlobalTheory

open GlobalTheory.TateCoker in

theorem tate_map_coker_card : ∀ (l : ℕ) [Fact l.Prime] (M N : Type) [CommGroup M] [CommGroup N] (φ : M →* N), (∀ x : M, ∃ y, y ^ l = x) → Function.Surjective φ → Finite φ.ker → Function.Injective (Tate.map l φ) ∧ Nat.card (Tate l N ⧸ LinearMap.range (Tate.map l φ)) = Nat.card {x : M // φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} := by
  intro l _ M N _ _ φ hd hs hf
  refine ⟨map_injective', ?_⟩
  have e1 : (Tate l N ⧸ LinearMap.range (Tate.map l φ)) ≃
      (Tate l N ⧸ (LinearMap.range (Tate.map l φ)).toAddSubgroup) := Equiv.refl _
  rw [Nat.card_congr e1, Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq (delta_ker hs)).symm.toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ (delta_surjective hs hd)).toEquiv]
  exact Nat.card_congr (Additive.toMul.trans (Equiv.refl _))

end GlobalTheory

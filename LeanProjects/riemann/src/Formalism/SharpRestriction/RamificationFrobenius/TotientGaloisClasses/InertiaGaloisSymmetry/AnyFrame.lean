import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.OfCharFrame

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

structure ModData where
  e : ℕ
  m : ℕ
  m_pos : 0 < m
  tower : 2 ^ (e + 2) ∣ m
  B : Type
  [grp : CommGroup B]
  ξ : (ZMod m)ˣ →* B

attribute [instance] ModData.grp

namespace ModData

variable (D : ModData)

instance neZero : NeZero D.m := ⟨D.m_pos.ne'⟩

def cl : (ZMod D.m)ˣ →* HGrp D.e := (QuotientGroup.mk' _).comp (ZMod.unitsMap D.tower)

theorem cl_apply (u : (ZMod D.m)ˣ) : D.cl u = hcl D.e (ZMod.unitsMap D.tower u) := rfl

def eta : (ZMod D.m)ˣ →* HGrp D.e × D.B := D.cl.prod D.ξ

theorem cl_neg_one : D.cl (-1) = 1 := by
  rw [cl_apply, D7.unitsMap_neg_one]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)

abbrev R : Type := D.eta.range

instance : Finite D.R := Finite.of_surjective _ D.eta.rangeRestrict_surjective

instance : Fintype (Additive D.R) := Fintype.ofFinite _

def p1 : D.R →* HGrp D.e := (MonoidHom.fst _ _).comp D.eta.range.subtype

def p2 : D.R →* D.B := (MonoidHom.snd _ _).comp D.eta.range.subtype

theorem eq_one_of {x : D.R} (h1 : D.p1 x = 1) (h2 : D.p2 x = 1) : x = 1 := Subtype.ext (Prod.ext h1 h2)

theorem projection_surjective : Function.Surjective D.p1 := by
  intro h
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective h
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective D.tower u
  refine ⟨⟨D.eta v, v, rfl⟩, ?_⟩
  show D.cl v = _
  rw [cl_apply, hv]
  rfl

theorem exists_gen : ∃ a : D.R, ∀ x : D.R, D.p2 x = 1 ↔ x ∈ Subgroup.zpowers a := by
  haveI : IsCyclic (HGrp D.e) := (hostGroup D.e).2.2.2.2.2.1
  have hinj : Function.Injective (D.p1.comp D.p2.ker.subtype) := by
    intro x y hxy
    have hxy' : D.p1 x.1 = D.p1 y.1 := hxy
    have h1 : D.p1 (x.1 * y.1⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy', mul_inv_cancel]
    have h2 : D.p2 (x.1 * y.1⁻¹) = 1 := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp x.2, MonoidHom.mem_ker.mp y.2, inv_one, mul_one]
    exact Subtype.ext (mul_inv_eq_one.mp (D.eq_one_of h1 h2))
  haveI : IsCyclic D.p2.ker := isCyclic_of_injective (D.p1.comp D.p2.ker.subtype) hinj
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D.p2.ker)
  refine ⟨g.1, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h3 := congrArg Subtype.val hk
    simpa using h3
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [map_zpow, MonoidHom.mem_ker.mp g.2, one_zpow]

def gen : D.R := D.exists_gen.choose

theorem gen_spec (x : D.R) : D.p2 x = 1 ↔ x ∈ Subgroup.zpowers D.gen := D.exists_gen.choose_spec x

def hA : Additive D.R →+ Additive (HGrp D.e) := MonoidHom.toAdditive D.p1

theorem hA_surj : Function.Surjective D.hA := D.projection_surjective

theorem hA_ker (k : ℤ) (hk : D.hA (k • Additive.ofMul D.gen) = 0) : k • Additive.ofMul D.gen = 0 := by
  rw [← ofMul_zpow] at hk ⊢
  have h2 : D.p2 (D.gen ^ k) = 1 := by
    rw [map_zpow, (D.gen_spec D.gen).mpr (Subgroup.mem_zpowers _), one_zpow]
  have h1 : D.p1 (D.gen ^ k) = 1 := by
    rw [← ofMul_eq_zero]
    exact hk
  rw [ofMul_eq_zero]
  exact D.eq_one_of h1 h2

def frame : Frame := Frame.ofGroup D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker

def isoA : D.frame.A ≃+ Additive D.R := Frame.ofGroupIso D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker

def iso : D.frame.MA ≃* D.R where
  toFun a := (D.isoA a.toAdd).toMul
  invFun x := Multiplicative.ofAdd (D.isoA.symm (Additive.ofMul x))
  left_inv a := by simp
  right_inv x := by simp
  map_mul' a b := by simp

theorem frame_e : D.frame.e = D.e := rfl

theorem hH_eq (a : D.frame.MA) : D.frame.hH a = D.p1 (D.iso a) := rfl

theorem iso_generator : D.iso (D.frame.iota D.frame.a0) = D.gen := by
  have h := Frame.ofGroup_generator D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker
  show (D.isoA D.frame.a0).toMul = D.gen
  exact congrArg Additive.toMul h

theorem ord_eq : D.frame.ord = Nat.card D.R := by
  rw [frame, Frame.ofGroup_ord, ← Nat.card_eq_fintype_card]
  rfl

def toA : (ZMod D.m)ˣ →* D.frame.MA := D.iso.symm.toMonoidHom.comp D.eta.rangeRestrict

theorem iso_toA (u : (ZMod D.m)ˣ) : D.iso (D.toA u) = D.eta.rangeRestrict u := D.iso.apply_symm_apply _

theorem toA_surj : Function.Surjective D.toA := D.iso.symm.surjective.comp (MonoidHom.rangeRestrict_surjective _)

theorem toA_eq_one_iff (u : (ZMod D.m)ˣ) : D.toA u = 1 ↔ D.eta u = 1 := by
  rw [← D.iso.injective.eq_iff, map_one, iso_toA, Subtype.ext_iff]
  rfl

theorem hH_toA (u : (ZMod D.m)ˣ) : D.frame.hH (D.toA u) = D.cl u := by
  rw [hH_eq, iso_toA]
  rfl

def xiA : D.frame.MA →* D.B := D.p2.comp D.iso.toMonoidHom

theorem xiA_toA (u : (ZMod D.m)ˣ) : D.xiA (D.toA u) = D.ξ u := by
  show D.p2 (D.iso (D.toA u)) = _
  rw [iso_toA]
  rfl

theorem mem_cusp_forms_iff_automorphic_compact (t : D.frame.A) : t ∈ D.frame.A0 ↔ D.xiA (D.frame.iota t) = 1 := by
  have ha0 : D.isoA D.frame.a0 = Additive.ofMul D.gen :=
    Frame.ofGroup_generator D.e D.hA D.hA_surj (Additive.ofMul D.gen) D.hA_ker
  show t ∈ AddSubgroup.zmultiples D.frame.a0 ↔ D.p2 ((D.isoA t).toMul) = 1
  rw [D.gen_spec, AddSubgroup.mem_zmultiples_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [map_zsmul, ha0]; rfl⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, D.isoA.injective ?_⟩
    rw [map_zsmul, ha0, ← ofMul_zpow, hk]
    rfl

theorem range_xiA : D.xiA.range = D.ξ.range := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨u, rfl⟩ := D.toA_surj a
    exact ⟨u, (D.xiA_toA u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨D.toA u, D.xiA_toA u⟩

theorem o_eq : D.frame.o = Nat.card D.ξ.range := by
  have hker : D.p2.ker = Subgroup.zpowers D.gen := by
    ext x
    exact D.gen_spec x
  have hn0 : D.frame.n0 = Nat.card D.p2.ker := by
    rw [hker, Nat.card_zpowers, frame, Frame.ofGroup_order, addOrderOf_ofMul_eq_orderOf]
  have hs : D.p2.range = D.ξ.range := by
    ext b
    constructor
    · rintro ⟨⟨_, v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨D.eta v, v, rfl⟩, rfl⟩
  have hmul := Subgroup.card_mul_index D.p2.ker
  rw [Subgroup.index_ker, hs] at hmul
  unfold Frame.o
  rw [ord_eq, hn0, ← hmul]
  have hpos : 0 < Nat.card D.p2.ker := Nat.card_pos
  exact Nat.mul_div_cancel_left _ hpos

theorem twoGroup (h : ∃ j : ℕ, ∀ u, D.ξ u ^ 2 ^ j = 1) : D.frame.TwoGroup := by
  obtain ⟨j, hj⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : Nat.card (HGrp D.e) = 2 ^ D.e := (hostGroup D.e).2.2.2.2.2.2.1
  have hp : IsPGroup 2 D.R := by
    intro x
    refine ⟨D.e + j, ?_⟩
    obtain ⟨_, u, rfl⟩ := x
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst]
      show (D.cl u) ^ 2 ^ (D.e + j) = 1
      rw [show 2 ^ (D.e + j) = Nat.card (HGrp D.e) * 2 ^ j by rw [hH, pow_add], pow_mul,
        pow_card_eq_one', one_pow]
    · rw [Prod.pow_snd]
      show (D.ξ u) ^ 2 ^ (D.e + j) = 1
      rw [show 2 ^ (D.e + j) = 2 ^ j * 2 ^ D.e by rw [pow_add, mul_comm], pow_mul, hj, one_pow]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  exact ⟨k, by rw [ord_eq, hk]⟩

def w : ℤˣ →* D.frame.MA := D.toA.comp (Units.map (Int.castRingHom (ZMod D.m)).toMonoidHom)

theorem w_neg_one : D.w (-1) = D.toA (-1) := by
  show D.toA (Units.map (Int.castRingHom (ZMod D.m)).toMonoidHom (-1)) = _
  congr 1
  ext
  simp

theorem w_mul_self (s : ℤˣ) : D.w s * D.w s = 1 := by
  rw [← map_mul, Int.units_mul_self, map_one]

theorem hH_w (s : ℤˣ) : D.frame.hH (D.w s) = 1 := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [map_one, map_one]
  · rw [w_neg_one, hH_toA, cl_neg_one]
    rfl

section Host

variable {q d : ℕ} (hH : HostHyp q d)

theorem m_dvd (q d : ℕ) : D.m ∣ D.m * q * d := ⟨q * d, by ring⟩
theorem q_dvd (q d : ℕ) : q ∣ D.m * q * d := ⟨D.m * d, by ring⟩
theorem d_dvd (q d : ℕ) : d ∣ D.m * q * d := ⟨D.m * q, by ring⟩

include hH in
theorem neZeroN : NeZero (D.m * q * d) := by
  have h1 := hH.1.pos
  have h2 := hH.2.1.pos
  have h3 := D.m_pos
  exact ⟨by positivity⟩

def art : (ZMod (D.m * q * d))ˣ →* D.frame.GG :=
  ((D7.sgnN hH.1 (D.q_dvd q d)).prod (D7.sgnN hH.2.1 (D.d_dvd q d))).prod
    (D.toA.comp (ZMod.unitsMap (D.m_dvd q d)) * D.w.comp (D7.sgnN hH.1 (D.q_dvd q d)))

theorem art_snd (u : (ZMod (D.m * q * d))ˣ) :
    (D.art hH u).2 = D.toA (ZMod.unitsMap (D.m_dvd q d) u) * D.w (D.art hH u).1.1 := rfl

theorem art_ps (u : (ZMod (D.m * q * d))ˣ) :
    (((D.art hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) q := by
  haveI := D.neZeroN hH
  exact D7.sgnN_val hH.1 (D.q_dvd q d) u

theorem art_ch (u : (ZMod (D.m * q * d))ˣ) :
    (((D.art hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) d := by
  haveI := D.neZeroN hH
  exact D7.sgnN_val hH.2.1 (D.d_dvd q d) u

theorem art_ps_one (u : (ZMod (D.m * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (D.m * q * d)).val ≡ y [MOD q])
    (hy : jacobiSym (y : ℤ) q = 1) : (D.art hH u).1.1 = 1 := by
  have h := D.art_ps hH u
  have h2 : jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) q = jacobiSym (y : ℤ) q := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ), ← Int.natCast_mod, ← Int.natCast_mod,
      show (u : ZMod (D.m * q * d)).val % q = y % q from hu]
  exact Units.ext (by rw [h, h2, hy]; rfl)

theorem art_ch_one (u : (ZMod (D.m * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (D.m * q * d)).val ≡ y [MOD d])
    (hy : jacobiSym (y : ℤ) d = 1) : (D.art hH u).1.2 = 1 := by
  have h := D.art_ch hH u
  have h2 : jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) d = jacobiSym (y : ℤ) d := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ), ← Int.natCast_mod, ← Int.natCast_mod,
      show (u : ZMod (D.m * q * d)).val % d = y % d from hu]
  exact Units.ext (by rw [h, h2, hy]; rfl)

theorem art_snd_one (u : (ZMod (D.m * q * d))ˣ) (hu : (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m]) :
    (D.art hH u).2 = D.w (D.art hH u).1.1 := by
  haveI := D.neZeroN hH
  have h1 : ZMod.unitsMap (D.m_dvd q d) u = 1 := by
    apply Units.ext
    rw [D7.unitsMap_val, Units.val_one]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
    simpa using h2
  rw [art_snd, h1, map_one, one_mul]

theorem art_eq_one (u : (ZMod (D.m * q * d))ˣ) (h1 : (D.art hH u).1.1 = 1) (h2 : (D.art hH u).1.2 = 1)
    (h3 : D.eta (ZMod.unitsMap (D.m_dvd q d) u) = 1) : D.art hH u = 1 := by
  refine Prod.ext (Prod.ext h1 h2) ?_
  rw [art_snd, h1, map_one, mul_one]
  exact (D.toA_eq_one_iff _).mpr h3

include hH in
theorem eta_one (u : (ZMod (D.m * q * d))ˣ) (hu : (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m]) :
    D.eta (ZMod.unitsMap (D.m_dvd q d) u) = 1 := by
  haveI := D.neZeroN hH
  have h1 : ZMod.unitsMap (D.m_dvd q d) u = 1 := by
    apply Units.ext
    rw [D7.unitsMap_val, Units.val_one]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
    simpa using h2
  rw [h1, map_one]

variable (hc : Nat.Coprime D.m (q * d))

include hc in
theorem art_surj : Function.Surjective (D.art hH) := by
  have := D.neZeroN hH
  intro g
  obtain ⟨v, hv⟩ := D.toA_surj (g.2 * D.w g.1.1)
  obtain ⟨y, cy, hy⟩ := D7.exists_sign hH.1 (D7.q4 hH) g.1.1
  obtain ⟨z, cz, hz⟩ := D7.exists_sign hH.2.1 (D7.d4 hH) g.1.2
  obtain ⟨u, h1, h2, h3⟩ := exists_unit_three hc.coprime_mul_right_right hc.coprime_mul_left_right (D7.cop_qd hH)
    (v : ZMod D.m).val y z (ZMod.val_coe_unit_coprime v) cy cz
  have h4 : (D.art hH u).1.1 = g.1.1 := Units.ext (by rw [art_ps, D7.jac_congr h2, hy])
  refine ⟨u, Prod.ext (Prod.ext h4 (Units.ext ?_)) ?_⟩
  · rw [art_ch, D7.jac_congr h3, hz]
  · rw [art_snd, (unitsMap_eq_iff _ u v).mpr h1, hv, h4, mul_assoc, w_mul_self, mul_one]

variable (he : 2 ≤ D.e) (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ D.m → jacobiSym (-(d : ℤ)) l = 1)

def charData : CharData D.frame where
  q := q
  d := d
  QS := D.m
  hyp := hH
  two_le_e := he
  QS_pos := D.m_pos
  tower_dvd := D.tower
  QS_coprime := hc
  QS_split := hs
  art := D.art hH
  art_surj := D.art_surj hH hc
  art_neg_one := by
    have h1 : (D.art hH (-1)).1.1 = -1 := D7.sgnN_neg_one hH.1 (D7.q4 hH) _
    refine Prod.ext (Prod.ext h1 (D7.sgnN_neg_one hH.2.1 (D7.d4 hH) _)) ?_
    rw [art_snd, D7.unitsMap_neg_one, h1, ← w_neg_one]
    exact D.w_mul_self _
  art_h := fun u v hv => by
    have := D.neZeroN hH
    rw [art_snd, map_mul, hH_w, mul_one, hH_toA, cl_apply, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
    exact congrArg (hcl D.e) (Units.ext ((D7.unitsMap_val _ u).trans hv.symm))
  art_d := fun u hu => by
    have h1 := D.art_ps_one hH u (hu.of_dvd (dvd_mul_left _ _)) (by simp)
    have h2 := D.art_snd_one hH u (hu.of_dvd (dvd_mul_right _ _))
    rw [h1, map_one] at h2
    rcases Int.units_eq_one_or (D.art hH u).1.2 with h3 | h3
    · exact Or.inl (Prod.ext (Prod.ext h1 h3) h2)
    · exact Or.inr (Prod.ext (Prod.ext h1 h3) h2)
  art_q := fun u hu => by
    have h2 := D.art_snd_one hH u (hu.of_dvd (dvd_mul_right _ _))
    refine Prod.ext (Prod.ext (Int.units_sq _) (Int.units_sq _)) ?_
    show (D.art hH u).2 ^ 2 = 1
    rw [h2, sq, w_mul_self]
  art_ch := D.art_ch hH

def host : HostRaw D.frame := (D.charData hH hc he hs).toHostRaw

theorem host_q : (D.host hH hc he hs).q = q := rfl
theorem host_d : (D.host hH hc he hs).d = d := rfl
theorem host_QS : (D.host hH hc he hs).QS = D.m := rfl
theorem host_art : (D.host hH hc he hs).art = D.art hH := rfl

theorem psQ : (D.host hH hc he hs).PsQ := D.art_ps hH

theorem exists_sqq : ∃ s : (D.host hH hc he hs).E, s ^ 2 = -((D.host hH hc he hs).q : (D.host hH hc he hs).E) ∧
    ∀ σ : (D.host hH hc he hs).E ≃ₐ[ℚ] (D.host hH hc he hs).E,
      σ s = (((((D.host hH hc he hs).gal σ).1.1 : ℤˣ) : ℤ) : (D.host hH hc he hs).E) * s :=
  (D.charData hH hc he hs).exists_sqq (D.psQ hH hc he hs)

theorem muPM (hq : q ≠ 3)
    (hmu : ∀ k : ℕ, k ∣ D.m → (∀ v : (ZMod D.m)ˣ, D.eta v = 1 → (v : ZMod D.m).val ≡ 1 [MOD k]) → k ∣ 2) : (D.host hH hc he hs).MuPM := by
  have := D.neZeroN hH
  refine (D.charData hH hc he hs).muPM fun k (hk : k ∣ D.m * q * d)
    (h : ∀ u : (ZMod (D.m * q * d))ˣ, D.art hH u = 1 → (u : ZMod (D.m * q * d)).val ≡ 1 [MOD k]) => ?_
  have hq2 := D7.q4 hH
  have hd2 := D7.d4 hH
  have c4 : ∀ p : ℕ, p % 4 = 3 → Nat.Coprime 4 p := fun p hp =>
    Nat.Coprime.pow_left 2 ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr (by omega)))
  have j4 : ∀ p : ℕ, p % 4 = 3 → jacobiSym ((4 : ℕ) : ℤ) p = 1 := fun p hp => by
    have h2 : Nat.Coprime 2 p := (Nat.coprime_two_left).mpr (Nat.odd_iff.mpr (by omega))
    exact jacobiSym.sq_one' (a := 2) h2
  have n4 : ∀ p : ℕ, p.Prime → p ≠ 3 → ¬ 4 ≡ 1 [MOD p] := fun p hp h3 h4 =>
    h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp ((Nat.modEq_iff_dvd' (by norm_num)).mp h4.symm))
  have ex := exists_unit_three hc.coprime_mul_right_right hc.coprime_mul_left_right (D7.cop_qd hH)
  have kq : Nat.Coprime k q := by
    refine ((Nat.Prime.coprime_iff_not_dvd hH.1).mpr fun hqk => ?_).symm
    obtain ⟨u, h1, h2, h3⟩ := ex 1 4 1 (Nat.coprime_one_left _) (c4 q hq2) (Nat.coprime_one_left _)
    have h4 := h u (D.art_eq_one hH u (D.art_ps_one hH u h2 (j4 q hq2)) (D.art_ch_one hH u h3 (by simp))
      (D.eta_one hH u h1))
    exact n4 q hH.1 hq (h2.symm.trans (h4.of_dvd hqk))
  have kd : Nat.Coprime k d := by
    refine ((Nat.Prime.coprime_iff_not_dvd hH.2.1).mpr fun hqk => ?_).symm
    obtain ⟨u, h1, h2, h3⟩ := ex 1 1 4 (Nat.coprime_one_left _) (Nat.coprime_one_left _) (c4 d hd2)
    have h4 := h u (D.art_eq_one hH u (D.art_ps_one hH u h2 (by simp)) (D.art_ch_one hH u h3 (j4 d hd2))
      (D.eta_one hH u h1))
    exact n4 d hH.2.1 (by have := hH.2.2.2.1; omega) (h3.symm.trans (h4.of_dvd hqk))
  have km : k ∣ D.m := kq.dvd_of_dvd_mul_right (kd.dvd_of_dvd_mul_right hk)
  refine hmu k km fun v hv => ?_
  obtain ⟨u, h1, h2, h3⟩ := ex (v : ZMod D.m).val 1 1 (ZMod.val_coe_unit_coprime _)
    (Nat.coprime_one_left _) (Nat.coprime_one_left _)
  have h4 := h u (D.art_eq_one hH u (D.art_ps_one hH u h2 (by simp)) (D.art_ch_one hH u h3 (by simp)) (by
    rw [(unitsMap_eq_iff _ u _).mpr h1, hv]))
  exact (h1.of_dvd km).symm.trans h4

theorem exact (h : ∀ l : ℕ, l.Prime → l ∣ D.m → ∃ v : (ZMod D.m)ˣ, (v : ZMod D.m).val ≡ 1 [MOD D.m / l] ∧ D.eta v ≠ 1) :
    (D.host hH hc he hs).Exact := by
  have := D.neZeroN hH
  intro l hl (hlm : l ∣ D.m)
  obtain ⟨v, hv, hv1⟩ := h l hl hlm
  obtain ⟨u, h1, h2, h3⟩ := exists_unit_three hc.coprime_mul_right_right hc.coprime_mul_left_right (D7.cop_qd hH)
    (v : ZMod D.m).val 1 1 (ZMod.val_coe_unit_coprime v) (Nat.coprime_one_left _) (Nat.coprime_one_left _)
  refine ⟨u, ?_, fun h4 => hv1 ?_⟩
  · show (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m * q * d / l]
    have h5 : D.m * q * d / l = D.m / l * (q * d) := by rw [mul_assoc, Nat.div_mul_right_comm hlm]
    have h6 : D.m / l ∣ D.m := Nat.div_dvd_of_dvd hlm
    rw [h5]
    exact (Nat.modEq_and_modEq_iff_modEq_mul (hc.coprime_dvd_left h6)).mp
      ⟨(h1.of_dvd h6).trans hv, (Nat.modEq_and_modEq_iff_modEq_mul (D7.cop_qd hH)).mp ⟨h2, h3⟩⟩
  · have h5 : (D.art hH u).2 = 1 := congrArg Prod.snd h4
    rw [art_snd, (unitsMap_eq_iff _ u v).mpr h1, D.art_ps_one hH u h2 (by simp), map_one, mul_one] at h5
    exact (D.toA_eq_one_iff v).mp h5

end Host

end ModData

end Formalism.HC

end

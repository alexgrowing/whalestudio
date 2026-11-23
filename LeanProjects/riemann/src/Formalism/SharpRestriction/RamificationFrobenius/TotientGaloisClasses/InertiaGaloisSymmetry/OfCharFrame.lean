import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.OfChar
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSymOfModEq
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

theorem unitsMap_eq_iff {M N : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (u : (ZMod N)ˣ) (v : (ZMod M)ˣ) :
    ZMod.unitsMap h u = v ↔ (u : ZMod N).val ≡ (v : ZMod M).val [MOD M] := by
  rw [Units.ext_iff, D7.unitsMap_val, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]

theorem unitsMap_eq_one_iff {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h u = 1 ↔ (u : ZMod N).val ≡ 1 [MOD M] := by
  haveI : NeZero M := ⟨by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd h)⟩
  rw [unitsMap_eq_iff h u 1, Units.val_one, ZMod.val_one_eq_one_mod]
  exact ⟨fun h1 => h1.trans (Nat.mod_modEq 1 M), fun h1 => h1.trans (Nat.mod_modEq 1 M).symm⟩

theorem unitsMap_val_modEq {M N : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (u : (ZMod N)ˣ) :
    (u : ZMod N).val ≡ ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M).val [MOD M] :=
  (unitsMap_eq_iff h u _).mp rfl

theorem exists_unit_three {a b c : ℕ} [NeZero (a * b * c)] (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c)
    (x y z : ℕ) (hx : Nat.Coprime x a) (hy : Nat.Coprime y b) (hz : Nat.Coprime z c) :
    ∃ u : (ZMod (a * b * c))ˣ, (u : ZMod (a * b * c)).val ≡ x [MOD a] ∧
      (u : ZMod (a * b * c)).val ≡ y [MOD b] ∧ (u : ZMod (a * b * c)).val ≡ z [MOD c] := by
  obtain ⟨t1, h1a, h1b⟩ := Nat.chineseRemainder hab x y
  obtain ⟨t, h2ab, h2c⟩ := Nat.chineseRemainder (Nat.Coprime.mul hac hbc) t1 z
  have hta : t ≡ x [MOD a] := (h2ab.of_mul_right b).trans h1a
  have htb : t ≡ y [MOD b] := (h2ab.of_mul_left a).trans h1b
  have hca : Nat.Coprime t a := hta.gcd_eq.trans hx
  have hcb : Nat.Coprime t b := htb.gcd_eq.trans hy
  have hcc : Nat.Coprime t c := h2c.gcd_eq.trans hz
  have hcop : Nat.Coprime t (a * b * c) := Nat.Coprime.mul_right (Nat.Coprime.mul_right hca hcb) hcc
  have hm := Nat.mod_modEq t (a * b * c)
  refine ⟨ZMod.unitOfCoprime t hcop, ?_, ?_, ?_⟩ <;> rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  · exact ((hm.of_mul_right c).of_mul_right b).trans hta
  · exact ((hm.of_mul_right c).of_mul_left a).trans htb
  · exact (hm.of_mul_left (a * b)).trans h2c

structure EvenData where
  e : ℕ
  m : ℕ
  m_pos : 0 < m
  tower : 2 ^ (e + 2) ∣ m
  B : Type
  [grp : CommGroup B]
  ξ : (ZMod m)ˣ →* B
  even : ξ (-1) = 1

attribute [instance] EvenData.grp

namespace EvenData

variable (D : EvenData)

instance neZero : NeZero D.m := ⟨D.m_pos.ne'⟩

def cl : (ZMod D.m)ˣ →* HGrp D.e := (QuotientGroup.mk' _).comp (ZMod.unitsMap D.tower)

theorem cl_apply (u : (ZMod D.m)ˣ) : D.cl u = hcl D.e (ZMod.unitsMap D.tower u) := rfl

def eta : (ZMod D.m)ˣ →* HGrp D.e × D.B := D.cl.prod D.ξ

theorem eta_neg_one : D.eta (-1) = 1 := by
  refine Prod.ext ?_ D.even
  show (QuotientGroup.mk' _) (ZMod.unitsMap D.tower (-1)) = 1
  rw [D7.unitsMap_neg_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_zpowers _

abbrev R : Type := D.eta.range

instance : Finite D.R := Finite.of_surjective _ D.eta.rangeRestrict_surjective

instance : Fintype (Additive D.R) := Fintype.ofFinite _

def p1 : D.R →* HGrp D.e := (MonoidHom.fst _ _).comp D.eta.range.subtype

def p2 : D.R →* D.B := (MonoidHom.snd _ _).comp D.eta.range.subtype

theorem eq_one_of {x : D.R} (h1 : D.p1 x = 1) (h2 : D.p2 x = 1) : x = 1 := by
  apply Subtype.ext
  exact Prod.ext h1 h2

theorem projection_surjective : Function.Surjective D.p1 := by
  intro h
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ h
  obtain ⟨u, rfl⟩ := ZMod.unitsMap_surjective D.tower w
  exact ⟨⟨D.eta u, u, rfl⟩, rfl⟩

theorem exists_gen : ∃ a : D.R, ∀ x : D.R, D.p2 x = 1 ↔ x ∈ Subgroup.zpowers a := by
  haveI : IsCyclic (HGrp D.e) := (Formalism.TwoAdicCyclotomicDecomposition.towerProperties.1.2.1 D.e).1
  let f : D.p2.ker →* HGrp D.e := D.p1.comp D.p2.ker.subtype
  have hf : Function.Injective f := (injective_iff_map_eq_one f).mpr fun x hx =>
    Subtype.ext (D.eq_one_of hx (MonoidHom.mem_ker.mp x.2))
  haveI : IsCyclic D.p2.ker := isCyclic_of_surjective (MonoidHom.ofInjective hf).symm (MulEquiv.surjective _)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D.p2.ker)
  refine ⟨g, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, MonoidHom.mem_ker.mpr hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact MonoidHom.mem_ker.mp (D.p2.ker.zpow_mem g.2 k)

def gen : D.R := D.exists_gen.choose

theorem gen_spec (x : D.R) : D.p2 x = 1 ↔ x ∈ Subgroup.zpowers D.gen := D.exists_gen.choose_spec x

def hA : Additive D.R →+ Additive (HGrp D.e) := MonoidHom.toAdditive D.p1

theorem hA_surj : Function.Surjective D.hA := by
  intro y
  obtain ⟨x, hx⟩ := D.projection_surjective (Additive.toMul y)
  exact ⟨Additive.ofMul x, hx⟩

theorem hA_ker (k : ℤ) (hk : D.hA (k • Additive.ofMul D.gen) = 0) : k • Additive.ofMul D.gen = 0 := by
  have h2 : D.p2 D.gen = 1 := (D.gen_spec D.gen).mpr (Subgroup.mem_zpowers _)
  have hk' : D.p1 (D.gen ^ k) = 1 := hk
  have h3 := D.eq_one_of hk' (by rw [map_zpow, h2, one_zpow])
  show Additive.ofMul (D.gen ^ k) = 0
  rw [h3]
  rfl

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

private theorem isoA_a0_eq_ofMul_gen : D.isoA D.frame.a0 = Additive.ofMul D.gen := by
  show (Fintype.equivFin (Additive D.R)).symm
    ((Fintype.equivFin (Additive D.R)).symm.symm (Additive.ofMul D.gen)) = _
  exact Equiv.apply_symm_apply _ _

theorem iso_generator : D.iso (D.frame.iota D.frame.a0) = D.gen := by
  show Additive.toMul (D.isoA D.frame.a0) = D.gen
  rw [isoA_a0_eq_ofMul_gen]
  rfl

theorem ord_eq : D.frame.ord = Nat.card D.R := by
  show Fintype.card (Additive D.R) = Nat.card D.R
  rw [← Nat.card_eq_fintype_card]
  rfl

def toA : (ZMod D.m)ˣ →* D.frame.MA := D.iso.symm.toMonoidHom.comp D.eta.rangeRestrict

theorem iso_toA (u : (ZMod D.m)ˣ) : D.iso (D.toA u) = D.eta.rangeRestrict u :=
  D.iso.apply_symm_apply _

theorem toA_surj : Function.Surjective D.toA :=
  D.iso.symm.surjective.comp D.eta.rangeRestrict_surjective

theorem toA_eq_one_iff (u : (ZMod D.m)ˣ) : D.toA u = 1 ↔ D.eta u = 1 := by
  rw [← D.iso.map_eq_one_iff, iso_toA, Subtype.ext_iff, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one]

theorem hH_toA (u : (ZMod D.m)ˣ) : D.frame.hH (D.toA u) = D.cl u := by
  rw [hH_eq, iso_toA]
  rfl

def xiA : D.frame.MA →* D.B := D.p2.comp D.iso.toMonoidHom

theorem xiA_toA (u : (ZMod D.m)ˣ) : D.xiA (D.toA u) = D.ξ u := by
  show D.p2 (D.iso (D.toA u)) = D.ξ u
  rw [iso_toA]
  rfl

theorem mem_cusp_forms_iff_automorphic_compact (t : D.frame.A) : t ∈ D.frame.A0 ↔ D.xiA (D.frame.iota t) = 1 := by
  show t ∈ AddSubgroup.zmultiples D.frame.a0 ↔ D.p2 (Additive.toMul (D.isoA t)) = 1
  rw [D.gen_spec, AddSubgroup.mem_zmultiples_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [map_zsmul, isoA_a0_eq_ofMul_gen, toMul_zsmul, toMul_ofMul]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, D.isoA.injective ?_⟩
    rw [map_zsmul, isoA_a0_eq_ofMul_gen, ← ofMul_zpow, hk, ofMul_toMul]

theorem range_xiA : D.xiA.range = D.ξ.range := by
  have h : D.ξ = D.xiA.comp D.toA := MonoidHom.ext fun u => (D.xiA_toA u).symm
  rw [h, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr D.toA_surj, ← MonoidHom.range_eq_map]

theorem o_eq : D.frame.o = Nat.card D.ξ.range := by
  have hz : Subgroup.zpowers D.gen = D.p2.ker :=
    Subgroup.ext fun x => (D.gen_spec x).symm.trans MonoidHom.mem_ker.symm
  have hn0 : D.frame.n0 = Nat.card D.p2.ker := by
    show addOrderOf D.frame.a0 = _
    rw [← addOrderOf_injective D.isoA.toAddMonoidHom D.isoA.injective D.frame.a0]
    show addOrderOf (D.isoA D.frame.a0) = _
    rw [isoA_a0_eq_ofMul_gen, addOrderOf_ofMul_eq_orderOf, ← Nat.card_zpowers, hz]
  have hr : D.p2.range = D.ξ.range := by
    rw [← D.range_xiA]
    show _ = (D.p2.comp D.iso.toMonoidHom).range
    have htop : D.iso.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr D.iso.surjective
    rw [MonoidHom.range_comp, htop, ← MonoidHom.range_eq_map]
  have hc : Nat.card D.R = Nat.card D.p2.range * Nat.card D.p2.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D.p2.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange D.p2).toEquiv]
  have hpos : 0 < Nat.card D.p2.ker := Nat.card_pos
  show D.frame.ord / D.frame.n0 = _
  rw [D.ord_eq, hn0, hc, Nat.mul_div_cancel _ hpos, hr]

theorem twoGroup (h : ∃ j : ℕ, ∀ u, D.ξ u ^ 2 ^ j = 1) : D.frame.TwoGroup := by
  obtain ⟨j, hj⟩ := h
  have hcard : Nat.card (HGrp D.e) = 2 ^ D.e := (Formalism.TwoAdicCyclotomicDecomposition.towerProperties.1.2.1 D.e).2.1
  have hpg : IsPGroup 2 D.R := by
    rintro ⟨_, u, rfl⟩
    refine ⟨D.e + j, ?_⟩
    apply Subtype.ext
    show D.eta u ^ 2 ^ (D.e + j) = 1
    refine Prod.ext ?_ ?_
    · show D.cl u ^ 2 ^ (D.e + j) = 1
      rw [show (2 : ℕ) ^ (D.e + j) = 2 ^ D.e * 2 ^ j from pow_add 2 D.e j, pow_mul, ← hcard,
        pow_card_eq_one', one_pow]
    · show D.ξ u ^ 2 ^ (D.e + j) = 1
      rw [show (2 : ℕ) ^ (D.e + j) = 2 ^ j * 2 ^ D.e by rw [pow_add, mul_comm], pow_mul, hj, one_pow]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  exact ⟨n, (D.ord_eq).trans hn⟩

section Host

variable {q d : ℕ} (hH : HostHyp q d)

theorem m_dvd (q d : ℕ) : D.m ∣ D.m * q * d := ⟨q * d, by ring⟩
theorem q_dvd (q d : ℕ) : q ∣ D.m * q * d := ⟨D.m * d, by ring⟩
theorem d_dvd (q d : ℕ) : d ∣ D.m * q * d := ⟨D.m * q, by ring⟩

include hH in
theorem neZeroN : NeZero (D.m * q * d) :=
  ⟨Nat.mul_ne_zero (Nat.mul_ne_zero D.m_pos.ne' hH.1.ne_zero) hH.2.1.ne_zero⟩

def art : (ZMod (D.m * q * d))ˣ →* D.frame.GG :=
  ((D7.sgnN hH.1 (D.q_dvd q d)).prod (D7.sgnN hH.2.1 (D.d_dvd q d))).prod (D.toA.comp (ZMod.unitsMap (D.m_dvd q d)))

theorem art_snd (u : (ZMod (D.m * q * d))ˣ) : (D.art hH u).2 = D.toA (ZMod.unitsMap (D.m_dvd q d) u) := rfl

theorem art_ps (u : (ZMod (D.m * q * d))ˣ) :
    (((D.art hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) q := by
  haveI := D.neZeroN hH
  haveI := Fact.mk hH.1
  show ((D7.sgnN hH.1 (D.q_dvd q d) u : ℤˣ) : ℤ) = _
  simp only [D7.sgnN, MonoidHom.coe_comp, Function.comp_apply, MulChar.coe_toUnitHom, D7.unitsMap_val]
  rw [← jacobiSym.legendreSym.to_jacobiSym q (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ)]
  simp [legendreSym]

theorem art_ch (u : (ZMod (D.m * q * d))ˣ) :
    (((D.art hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) d := by
  haveI := D.neZeroN hH
  haveI := Fact.mk hH.2.1
  show ((D7.sgnN hH.2.1 (D.d_dvd q d) u : ℤˣ) : ℤ) = _
  simp only [D7.sgnN, MonoidHom.coe_comp, Function.comp_apply, MulChar.coe_toUnitHom, D7.unitsMap_val]
  rw [← jacobiSym.legendreSym.to_jacobiSym d (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ)]
  simp [legendreSym]

theorem art_ps_one (u : (ZMod (D.m * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (D.m * q * d)).val ≡ y [MOD q])
    (hy : jacobiSym (y : ℤ) q = 1) : (D.art hH u).1.1 = 1 := by
  have h1 := D.art_ps hH u
  have h2 : jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) q = jacobiSym (y : ℤ) q := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ)]
    congr 1
    exact_mod_cast (hu : _ % q = _ % q)
  rw [h2, hy] at h1
  exact Units.ext h1

theorem art_ch_one (u : (ZMod (D.m * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (D.m * q * d)).val ≡ y [MOD d])
    (hy : jacobiSym (y : ℤ) d = 1) : (D.art hH u).1.2 = 1 := by
  have h1 := D.art_ch hH u
  have h2 : jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) d = jacobiSym (y : ℤ) d := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ)]
    congr 1
    exact_mod_cast (hu : _ % d = _ % d)
  rw [h2, hy] at h1
  exact Units.ext h1

theorem art_snd_one (u : (ZMod (D.m * q * d))ˣ) (hu : (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m]) : (D.art hH u).2 = 1 := by
  haveI := D.neZeroN hH
  rw [art_snd, (unitsMap_eq_one_iff _ u).mpr hu, map_one]

variable (hc : Nat.Coprime D.m (q * d))

include hc in
theorem art_surj : Function.Surjective (D.art hH) := by
  have hsgn : ∀ {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (s : ℤˣ),
      ∃ y : ℕ, Nat.Coprime y p ∧ jacobiSym (y : ℤ) p = (s : ℤ) := by
    intro p hp hp4 s
    rcases Int.units_eq_one_or s with rfl | rfl
    · exact ⟨1, Nat.coprime_one_left p, by simp⟩
    · have h2 := hp.two_le
      refine ⟨p - 1, ?_, ?_⟩
      · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      · have hodd : Odd p := hp.odd_of_ne_two (by omega)
        have e : ((p - 1 : ℕ) : ℤ) % (p : ℤ) = (-1 : ℤ) % (p : ℤ) := by
          rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
          push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
          simp
        rw [jacobiSym.mod_left, e, ← jacobiSym.mod_left, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four hp4]
        simp
  haveI := D.neZeroN hH
  rintro ⟨⟨s1, s2⟩, a⟩
  obtain ⟨w, rfl⟩ := D.toA_surj a
  obtain ⟨y, hy, hys⟩ := hsgn hH.1 (D7.q4 hH) s1
  obtain ⟨z, hz, hzs⟩ := hsgn hH.2.1 (D7.d4 hH) s2
  have hqd : Nat.Coprime q d := (Nat.coprime_primes hH.1 hH.2.1).mpr (by
    intro h
    have h1 := hH.2.2.1
    have h2 := hH.2.2.2.1
    subst h
    omega)
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_unit_three (a := D.m) (b := q) (c := d)
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right q d) hc) (Nat.Coprime.coprime_dvd_right (dvd_mul_left d q) hc) hqd
    _ y z (ZMod.val_coe_unit_coprime w) hy hz
  refine ⟨u, Prod.ext (Prod.ext ?_ ?_) ?_⟩
  · show (D.art hH u).1.1 = s1
    apply Units.ext
    rw [D.art_ps hH u, jacobiSym.mod_left, ← hys, jacobiSym.mod_left (y : ℤ)]
    congr 1
    exact_mod_cast (hu2 : _ % q = _ % q)
  · show (D.art hH u).1.2 = s2
    apply Units.ext
    rw [D.art_ch hH u, jacobiSym.mod_left, ← hzs, jacobiSym.mod_left (z : ℤ)]
    congr 1
    exact_mod_cast (hu3 : _ % d = _ % d)
  · show D.toA (ZMod.unitsMap (D.m_dvd q d) u) = D.toA w
    rw [(unitsMap_eq_iff _ u w).mpr hu1]

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
    refine Prod.ext (Prod.ext (D7.sgnN_neg_one hH.1 (D7.q4 hH) _) (D7.sgnN_neg_one hH.2.1 (D7.d4 hH) _)) ?_
    rw [art_snd, D7.unitsMap_neg_one]
    exact (D.toA_eq_one_iff _).mpr D.eta_neg_one
  art_h := fun u v hv => by
    have := D.neZeroN hH
    rw [art_snd, hH_toA, cl_apply, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
    exact congrArg (hcl D.e) (Units.ext ((D7.unitsMap_val _ u).trans hv.symm))
  art_d := fun u hu => by
    have h1 := D.art_ps_one hH u (hu.of_dvd (dvd_mul_left _ _)) (by simp)
    have h2 := D.art_snd_one hH u (hu.of_dvd (dvd_mul_right _ _))
    rcases Int.units_eq_one_or (D.art hH u).1.2 with h3 | h3
    · exact Or.inl (Prod.ext (Prod.ext h1 h3) h2)
    · exact Or.inr (Prod.ext (Prod.ext h1 h3) h2)
  art_q := fun u hu => by
    have h2 := D.art_snd_one hH u (hu.of_dvd (dvd_mul_right _ _))
    refine Prod.ext (Prod.ext (Int.units_sq _) (Int.units_sq _)) ?_
    show (D.art hH u).2 ^ 2 = 1
    rw [h2, one_pow]
  art_ch := D.art_ch hH

def host : HostRaw D.frame := (D.charData hH hc he hs).toHostRaw

theorem host_q : (D.host hH hc he hs).q = q := rfl
theorem host_d : (D.host hH hc he hs).d = d := rfl
theorem host_QS : (D.host hH hc he hs).QS = D.m := rfl
theorem host_art : (D.host hH hc he hs).art = D.art hH := rfl

theorem psQ : (D.host hH hc he hs).PsQ := by
  intro u
  exact D.art_ps hH u

theorem exists_sqq : ∃ s : (D.host hH hc he hs).E, s ^ 2 = -((D.host hH hc he hs).q : (D.host hH hc he hs).E) ∧
    ∀ σ : (D.host hH hc he hs).E ≃ₐ[ℚ] (D.host hH hc he hs).E,
      σ s = (((((D.host hH hc he hs).gal σ).1.1 : ℤˣ) : ℤ) : (D.host hH hc he hs).E) * s :=
  (D.charData hH hc he hs).exists_sqq (D.psQ hH hc he hs)

theorem muPM (hq : q ≠ 3) : (D.host hH hc he hs).MuPM := by
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
    have h4 := h u (Prod.ext (Prod.ext (D.art_ps_one hH u h2 (j4 q hq2)) (D.art_ch_one hH u h3 (by simp)))
      (D.art_snd_one hH u h1))
    exact n4 q hH.1 hq (h2.symm.trans (h4.of_dvd hqk))
  have kd : Nat.Coprime k d := by
    refine ((Nat.Prime.coprime_iff_not_dvd hH.2.1).mpr fun hqk => ?_).symm
    obtain ⟨u, h1, h2, h3⟩ := ex 1 1 4 (Nat.coprime_one_left _) (Nat.coprime_one_left _) (c4 d hd2)
    have h4 := h u (Prod.ext (Prod.ext (D.art_ps_one hH u h2 (by simp)) (D.art_ch_one hH u h3 (j4 d hd2)))
      (D.art_snd_one hH u h1))
    exact n4 d hH.2.1 (by have := hH.2.2.2.1; omega) (h3.symm.trans (h4.of_dvd hqk))
  have km : k ∣ D.m := kq.dvd_of_dvd_mul_right (kd.dvd_of_dvd_mul_right hk)
  obtain ⟨u, h1, h2, h3⟩ := ex ((-1 : (ZMod D.m)ˣ) : ZMod D.m).val 1 1 (ZMod.val_coe_unit_coprime _)
    (Nat.coprime_one_left _) (Nat.coprime_one_left _)
  have h4 := h u (Prod.ext (Prod.ext (D.art_ps_one hH u h2 (by simp)) (D.art_ch_one hH u h3 (by simp))) (by
    rw [art_snd, (unitsMap_eq_iff _ u _).mpr h1]
    exact (D.toA_eq_one_iff _).mpr D.eta_neg_one))
  have h5 := (unitsMap_eq_one_iff km (-1)).mpr ((h1.of_dvd km).symm.trans h4)
  rw [D7.unitsMap_neg_one, Units.ext_iff, Units.val_neg, Units.val_one] at h5
  refine (ZMod.natCast_eq_zero_iff 2 k).mp ?_
  push_cast
  linear_combination -h5

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
    rw [art_snd, (unitsMap_eq_iff _ u v).mpr h1] at h5
    exact (D.toA_eq_one_iff v).mp h5

end Host

end EvenData

end Formalism.HC

end

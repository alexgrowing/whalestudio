import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.AnyLevel

open Formalism.HC Formalism.FrobeniusOrbits UpperTheory.Top

private theorem ann_zpowers {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (u : (ZMod M)ˣ) :
    u ∈ EvenGrp.ann (Subgroup.zpowers χ) ↔ χ u = 1 := by
  rw [EvenGrp.mem_ann]
  constructor
  · intro h
    exact h χ (Subgroup.mem_zpowers χ)
  · intro h ψ hψ
    rw [Subgroup.zpowers_eq_closure] at hψ
    induction hψ using Subgroup.closure_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact h
    | one => exact MulChar.one_apply_coe u
    | mul x y _ _ hx hy => rw [MulChar.mul_apply, hx, hy, one_mul]
    | inv x _ hx => rw [MulChar.inv_apply_eq_inv', hx, inv_one]

private theorem xiW_eq_one {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (e : ℕ)
    (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) :
    EvenGrp.xiW (Subgroup.zpowers χ) e u = 1 ↔ χ (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u : (ZMod M)ˣ) = 1 := by
  change QuotientGroup.mk' _ (ZMod.unitsMap (Nat.dvd_lcm_right (2 ^ (e + 2)) M) u) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ann_zpowers]

private theorem dvd_QS {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (hχ : χ.IsPrimitive) (e : ℕ) :
    M ∣ EvenGrp.QS (Subgroup.zpowers χ) e := by
  obtain ⟨hQL, h2Q, hgood⟩ := EvenGrp.good_QS (Subgroup.zpowers χ) e
  set Q := EvenGrp.QS (Subgroup.zpowers χ) e with hQ
  haveI : NeZero ((2 ^ (e + 2)).lcm M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩
  have hf : χ.FactorsThrough (Q.gcd M) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.gcd_dvd_right Q M)).mpr ?_
    intro x hx
    rw [MonoidHom.mem_ker, unitsMap_eq_one_iff] at hx
    obtain ⟨z, hz1, hz2⟩ := Nat.chineseRemainder' hx.symm
    have hzM : z.Coprime M := hz2.gcd_eq.trans (ZMod.val_coe_unit_coprime x)
    have hzQ : z.Coprime Q := hz1.gcd_eq.trans (Nat.gcd_one_left Q)
    have hz2e : z.Coprime (2 ^ (e + 2)) := hzQ.coprime_dvd_right h2Q
    have hzL : z.Coprime ((2 ^ (e + 2)).lcm M) :=
      (Nat.Coprime.mul_right hz2e hzM).coprime_dvd_right (Nat.lcm_dvd_mul _ _)
    have hw := hgood (ZMod.unitOfCoprime z hzL) (by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact ((Nat.mod_modEq z _).of_dvd hQL).trans hz1)
    rw [xiW_eq_one, unitsMap_unitOfCoprime] at hw
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    have hx' : ((ZMod.unitOfCoprime z (hzL.coprime_dvd_right (Nat.dvd_lcm_right _ _)) : (ZMod M)ˣ) : ZMod M) = x := by
      rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (x : ZMod M)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hz2
    rw [← hx']
    exact hw
  have hc0 : χ.conductor ≤ Q.gcd M := Nat.sInf_le hf
  have hχ' : χ.conductor = M := hχ
  rw [hχ'] at hc0
  have hg : Q.gcd M = M :=
    le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.gcd_dvd_right _ _)) hc0
  have h := Nat.gcd_dvd_left Q M
  rwa [hg] at h

private theorem hcl_nat (e a : ℕ) (h : a.Coprime (2 ^ (e + 2))) :
    hcl e (ZMod.unitOfCoprime a h) = 1 ↔ (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) := by
  have h1 : hcl e 1 = 1 := rfl
  rw [← h1, hcl_eq_hcl_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg,
    Units.val_one]
  apply or_congr
  · rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  · rw [eq_neg_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add, ZMod.natCast_eq_zero_iff,
      Nat.modEq_zero_iff_dvd]

private theorem art_iff (D : ModData) {q d : ℕ} (hH : HostHyp q d) (a : ℕ) (h : a.Coprime (D.m * q * d)) :
    D.art hH (ZMod.unitOfCoprime a h) = 1 ↔
      D.eta (ZMod.unitOfCoprime a (h.coprime_dvd_right (D.m_dvd q d))) = 1 ∧
        jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1 := by
  have hv : ((ZMod.unitOfCoprime a h : ZMod (D.m * q * d)).val) ≡ a [MOD D.m * q * d] := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_modEq a _
  have jq : jacobiSym (((ZMod.unitOfCoprime a h : ZMod (D.m * q * d)).val : ℕ) : ℤ) q =
      jacobiSym (a : ℤ) q := D7.jac_congr (hv.of_dvd (D.q_dvd q d))
  have jd : jacobiSym (((ZMod.unitOfCoprime a h : ZMod (D.m * q * d)).val : ℕ) : ℤ) d =
      jacobiSym (a : ℤ) d := D7.jac_congr (hv.of_dvd (D.d_dvd q d))
  have hm : ZMod.unitsMap (D.m_dvd q d) (ZMod.unitOfCoprime a h) =
      ZMod.unitOfCoprime a (h.coprime_dvd_right (D.m_dvd q d)) := unitsMap_unitOfCoprime _ _ _
  constructor
  · intro h1
    have a1 : (D.art hH (ZMod.unitOfCoprime a h)).1.1 = 1 := by rw [h1]; rfl
    have a2 : (D.art hH (ZMod.unitOfCoprime a h)).1.2 = 1 := by rw [h1]; rfl
    have a3 : (D.art hH (ZMod.unitOfCoprime a h)).2 = 1 := by rw [h1]; rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [D.art_snd, a1, map_one, mul_one, D.toA_eq_one_iff, hm] at a3
      exact a3
    · rw [← jq, ← D.art_ps hH, a1, Units.val_one]
    · rw [← jd, ← D.art_ch hH, a2, Units.val_one]
  · rintro ⟨he, hq, hd⟩
    apply D.art_eq_one
    · apply Units.ext
      rw [D.art_ps, jq, hq, Units.val_one]
    · apply Units.ext
      rw [D.art_ch, jd, hd, Units.val_one]
    · rw [hm]
      exact he

theorem UpperTheory.Top.kerChiAny :
    ∀ (ψ : PChar) (e q d : ℕ) (hH : HostHyp q d) (hc : Nat.Coprime ψ.N (q * d)) (he : 2 ≤ e)
      (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ ψ.N → jacobiSym (-(d : ℤ)) l = 1),
      KerChi ψ (AnyGrp.host (Subgroup.zpowers ψ.χ) e hH hc he hs) := by
  intro ψ e q d hH hc he hs
  haveI := ψ.ne
  set D := AnyGrp.data (Subgroup.zpowers ψ.χ) e with hD
  have hM : ψ.N ∣ D.m := dvd_QS ψ.χ ψ.prim e
  refine ⟨hM, fun a h => ?_⟩
  have h' : a.Coprime (D.m * q * d) := h
  change D.art hH (ZMod.unitOfCoprime a h') = 1 ↔
    (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ ψ.val a = 1 ∧
      jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1
  refine (art_iff D hH a h').trans ?_
  have h1 : a.Coprime D.m := h'.coprime_dvd_right (D.m_dvd q d)
  have hT : 2 ^ (e + 2) ∣ D.m := D.tower
  have h2 : a.Coprime (2 ^ (e + 2)) := h1.coprime_dvd_right hT
  have hL : (2 ^ (e + 2)).lcm ψ.N ∣ D.m := Nat.lcm_dvd hT hM
  have hcL : a.Coprime ((2 ^ (e + 2)).lcm ψ.N) := h1.coprime_dvd_right hL
  have hcl1 : D.cl (ZMod.unitOfCoprime a h1) = hcl e (ZMod.unitOfCoprime a h2) := by
    rw [ModData.cl, MonoidHom.comp_apply, unitsMap_unitOfCoprime]
    rfl
  have hxi : D.ξ (ZMod.unitOfCoprime a h1) =
      EvenGrp.xiW (Subgroup.zpowers ψ.χ) e (ZMod.unitOfCoprime a hcL) := by
    rw [← EvenGrp.xi_unitsMap, unitsMap_unitOfCoprime]
    rfl
  have hw : EvenGrp.xiW (Subgroup.zpowers ψ.χ) e (ZMod.unitOfCoprime a hcL) = 1 ↔ ψ.val a = 1 := by
    rw [xiW_eq_one, unitsMap_unitOfCoprime, ZMod.coe_unitOfCoprime]
    rfl
  have key : D.eta (ZMod.unitOfCoprime a h1) = 1 ↔
      (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ ψ.val a = 1 := by
    rw [ModData.eta, MonoidHom.prod_apply, Prod.mk_eq_one]
    refine Iff.and ?_ ?_
    · rw [hcl1]
      exact hcl_nat e a h2
    · rw [hxi]
      exact hw
  rw [key, and_assoc]

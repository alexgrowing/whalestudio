import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.OfCharFrame
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

theorem unitsMap_unitOfCoprime {M N : ℕ} (h : M ∣ N) (a : ℕ) (ha : Nat.Coprime a N) :
    ZMod.unitsMap h (ZMod.unitOfCoprime a ha) = ZMod.unitOfCoprime a (ha.coprime_dvd_right h) := by
  ext
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, ZMod.cast_natCast h]

theorem HostRaw.art_eq_of_prim_eq {φ : Frame} (H : HostRaw φ) {θ θ' : φ.Char} (h : H.prim θ = H.prim θ')
    (u : (ZMod H.condN)ˣ) : θ (H.art u) = θ' (H.art u) := by
  have h1 := (H.isPrimOf_prim θ).2 _ (ZMod.val_coe_unit_coprime u)
  have h2 := ((H.isPrimOf_iff θ' _).mpr h).2 _ (ZMod.val_coe_unit_coprime u)
  have h3 := h1.symm.trans h2
  rw [HostRaw.dirAt, HostRaw.dirAt, ZMod.natCast_zmod_val, H.dir_unit, H.dir_unit] at h3
  exact Units.ext h3

namespace EvenGrp

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)

def ann : Subgroup (ZMod M)ˣ := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ).symm (OrderDual.toDual Ξ)

theorem mem_ann (u : (ZMod M)ˣ) : u ∈ ann Ξ ↔ ∀ χ ∈ Ξ, χ u = 1 := by
  simp [ann]

theorem mem_iff (χ : DirichletCharacter ℂ M) : χ ∈ Ξ ↔ ∀ u ∈ ann Ξ, χ u = 1 := by
  have h1 := (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ).apply_symm_apply (OrderDual.toDual Ξ)
  have h2 : χ ∈ Ξ ↔ χ ∈ OrderDual.ofDual ((MulChar.subgroupOrderIsoSubgroupMulChar (ZMod M) ℂ) (ann Ξ)) := by
    simp only [ann, h1, OrderDual.ofDual_toDual]
  rw [h2]
  generalize ann Ξ = S
  simp

abbrev B : Type := (ZMod M)ˣ ⧸ ann Ξ

theorem card_B : Nat.card (B Ξ) = Nat.card Ξ := by
  rw [← MulChar.card_subgroupOrderIsoSubgroupMulChar (R := ℂ), ann, OrderIso.apply_symm_apply]
  rfl

instance neZero_lcm : NeZero (Nat.lcm (2 ^ (e + 2)) M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩

def xiW : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ →* B Ξ := (QuotientGroup.mk' _).comp (ZMod.unitsMap (Nat.dvd_lcm_right _ _))

theorem xiW_surj : Function.Surjective (xiW Ξ e) := by
  intro b
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (ann Ξ) b
  obtain ⟨c, rfl⟩ := ZMod.unitsMap_surjective (Nat.dvd_lcm_right (2 ^ (e + 2)) M) a
  exact ⟨c, rfl⟩

def Good (m : ℕ) : Prop := m ∣ Nat.lcm (2 ^ (e + 2)) M ∧ 2 ^ (e + 2) ∣ m ∧
  ∀ u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ, (u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val ≡ 1 [MOD m] → xiW Ξ e u = 1

theorem exists_good : ∃ m, Good Ξ e m := by
  refine ⟨Nat.lcm (2 ^ (e + 2)) M, dvd_rfl, Nat.dvd_lcm_left _ _, fun u hu => ?_⟩
  have h1 : ((u : ZMod (Nat.lcm (2 ^ (e + 2)) M)).val : ZMod (Nat.lcm (2 ^ (e + 2)) M)) =
      ((1 : ℕ) : ZMod (Nat.lcm (2 ^ (e + 2)) M)) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
  rw [ZMod.natCast_zmod_val, Nat.cast_one] at h1
  have h2 : u = 1 := Units.ext (by rw [h1, Units.val_one])
  rw [h2, map_one]

open Classical in

def QS : ℕ := Nat.find (exists_good Ξ e)

open Classical in
theorem good_QS : Good Ξ e (QS Ξ e) := Nat.find_spec (exists_good Ξ e)

open Classical in
theorem not_good {m : ℕ} (h : m < QS Ξ e) : ¬ Good Ξ e m := Nat.find_min (exists_good Ξ e) h

theorem QS_dvd : QS Ξ e ∣ Nat.lcm (2 ^ (e + 2)) M := (good_QS Ξ e).1

theorem QS_dvd_mul : QS Ξ e ∣ 2 ^ (e + 2) * M :=
  (QS_dvd Ξ e).trans (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))

theorem QS_pos : 0 < QS Ξ e := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have h1 := QS_dvd Ξ e
  rw [h, zero_dvd_iff] at h1
  exact (NeZero.ne _) h1

instance neZero_QS : NeZero (QS Ξ e) := ⟨(QS_pos Ξ e).ne'⟩

def xi : (ZMod (QS Ξ e))ˣ →* B Ξ :=
  (ZMod.unitsMap (QS_dvd Ξ e)).liftOfSurjective (ZMod.unitsMap_surjective _)
    ⟨xiW Ξ e, fun u hu => (good_QS Ξ e).2.2 u ((unitsMap_eq_one_iff _ u).mp hu)⟩

theorem xi_unitsMap (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) : xi Ξ e (ZMod.unitsMap (QS_dvd Ξ e) u) = xiW Ξ e u :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem xi_surj : Function.Surjective (xi Ξ e) := by
  intro b
  obtain ⟨u, rfl⟩ := xiW_surj Ξ e b
  exact ⟨_, xi_unitsMap Ξ e u⟩

variable (hev : ∀ χ ∈ Ξ, χ.Even)

def data : EvenData where
  e := e
  m := QS Ξ e
  m_pos := QS_pos Ξ e
  tower := (good_QS Ξ e).2.1
  B := B Ξ
  ξ := xi Ξ e
  even := by
    rw [← D7.unitsMap_neg_one (QS_dvd Ξ e), xi_unitsMap]
    show ((ZMod.unitsMap _ (-1) : (ZMod M)ˣ) : B Ξ) = 1
    rw [D7.unitsMap_neg_one, QuotientGroup.eq_one_iff, mem_ann]
    exact hev

def frame : Frame := (data Ξ e hev).frame

theorem frame_e : (frame Ξ e hev).e = e := rfl

theorem o_eq : (frame Ξ e hev).o = Nat.card Ξ := by
  rw [← card_B Ξ]
  refine ((data Ξ e hev).o_eq).trans ?_
  show Nat.card (xi Ξ e).range = Nat.card (B Ξ)
  rw [MonoidHom.range_eq_top.mpr (xi_surj Ξ e)]
  exact Nat.card_congr Subgroup.topEquiv.toEquiv

theorem twoGroup (h : ∃ j : ℕ, Nat.card Ξ = 2 ^ j) : (frame Ξ e hev).TwoGroup := by
  obtain ⟨j, hj⟩ := h
  have hU : Nat.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega),
      show e + 2 - 1 = e + 1 by omega]
    norm_num
  have h2 : Nat.card (HGrp e) ∣ 2 ^ (e + 1) := by
    have h0 := Subgroup.card_quotient_dvd_card (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
    rwa [hU] at h0
  have hB : Nat.card (B Ξ) = 2 ^ j := (card_B Ξ).trans hj
  have h3 : Nat.card (data Ξ e hev).R ∣ 2 ^ (e + 1 + j) := by
    have h1 : Nat.card (data Ξ e hev).R ∣ Nat.card (HGrp e × B Ξ) := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_prod, hB] at h1
    rw [pow_add]
    exact h1.trans (mul_dvd_mul_right h2 _)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  exact ⟨k, ((data Ξ e hev).ord_eq).trans hk⟩

theorem QS_le (h : 4 * M ≤ 2 ^ e) : QS Ξ e ≤ (frame Ξ e hev).ord ^ 2 := by
  have h1 := Nat.le_of_dvd (Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero (NeZero.ne M))) (QS_dvd_mul Ξ e)
  have h2 : 2 ^ e ≤ (frame Ξ e hev).ord := (frame Ξ e hev).two_pow_le_ord
  calc QS Ξ e ≤ 2 ^ e * (4 * M) := by rw [pow_add] at h1; linarith
    _ ≤ 2 ^ e * 2 ^ e := Nat.mul_le_mul_left _ h
    _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul h2 h2

theorem dvd_of_dvd_QS {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (h : l ∣ QS Ξ e) : l ∣ M := by
  rcases (Nat.Prime.dvd_mul hl).mp (h.trans (QS_dvd_mul Ξ e)) with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h1)) h2
  · exact h1

theorem exact_data (he : 1 ≤ e) (l : ℕ) (hl : l.Prime) (hd : l ∣ QS Ξ e) :
    ∃ v : (ZMod (QS Ξ e))ˣ, (v : ZMod (QS Ξ e)).val ≡ 1 [MOD QS Ξ e / l] ∧ (data Ξ e hev).eta v ≠ 1 := by
  have hlt : QS Ξ e / l < QS Ξ e := Nat.div_lt_self (QS_pos Ξ e) hl.one_lt
  have hdv : QS Ξ e / l ∣ QS Ξ e := Nat.div_dvd_of_dvd hd
  by_cases h2 : 2 ^ (e + 2) ∣ QS Ξ e / l
  · by_contra hn
    refine not_good Ξ e hlt ⟨hdv.trans (QS_dvd Ξ e), h2, fun u hu => ?_⟩
    by_contra h3
    refine hn ⟨ZMod.unitsMap (QS_dvd Ξ e) u, ((unitsMap_val_modEq (QS_dvd Ξ e) u).of_dvd hdv).symm.trans hu, fun h4 => h3 ?_⟩
    rw [← xi_unitsMap]
    exact congrArg Prod.snd h4
  · obtain ⟨c, hc⟩ := (good_QS Ξ e).2.1
    have hl2 : l = 2 := by
      by_contra h3
      have h4 : Nat.Coprime (2 ^ (e + 2)) l := Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm h3))
      exact h2 (h4.dvd_of_dvd_mul_right (by rw [Nat.div_mul_cancel hd]; exact (good_QS Ξ e).2.1))
    subst hl2
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have hdiv : QS Ξ (k + 1) / 2 = 2 ^ (k + 2) * c := by
      rw [hc, show 2 ^ (k + 1 + 2) * c = 2 * (2 ^ (k + 2) * c) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    have hQ : QS Ξ (k + 1) = 2 * (2 ^ (k + 2) * c) := by rw [hc]; ring
    have hcop : Nat.Coprime (2 ^ (k + 2) * c + 1) (QS Ξ (k + 1)) := by
      rw [hQ]
      refine Nat.Coprime.mul_right ?_ (by simp)
      rw [Nat.coprime_two_right]
      exact ⟨2 ^ (k + 1) * c, by ring⟩
    have hval : ((ZMod.unitOfCoprime _ hcop : (ZMod (QS Ξ (k + 1)))ˣ) : ZMod (QS Ξ (k + 1))).val ≡ 2 ^ (k + 2) * c + 1
        [MOD QS Ξ (k + 1)] := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact Nat.mod_modEq _ _
    refine ⟨ZMod.unitOfCoprime _ hcop, (hval.of_dvd hdv).trans ?_, fun h4 => ?_⟩
    · rw [hdiv]
      simp [Nat.ModEq]
    · have h5 : hcl (k + 1) (ZMod.unitsMap (good_QS Ξ (k + 1)).2.1 (ZMod.unitOfCoprime _ hcop)) = hcl (k + 1) 1 :=
        congrArg Prod.fst h4
      rw [unitsMap_unitOfCoprime, hcl_eq_hcl_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg,
        Units.val_one, Nat.cast_add, Nat.cast_one] at h5
      rcases h5 with h5 | h5
      · refine h2 ?_
        rw [hdiv, ← ZMod.natCast_eq_zero_iff]
        linear_combination h5
      · have h6 : 2 ^ (k + 1 + 2) ∣ 2 ^ (k + 2) * c + 2 := by
          rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_ofNat]
          linear_combination h5
        have h7 : 4 ∣ 2 ^ (k + 2) * c + 2 := Dvd.dvd.trans ⟨2 ^ (k + 1), by ring⟩ h6
        have h8 : 4 ∣ 2 ^ (k + 2) * c := ⟨2 ^ k * c, by ring⟩
        omega

def thetaB (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : B Ξ →* ℂˣ :=
  QuotientGroup.lift (ann Ξ) χ.toUnitHom fun u hu =>
    Units.ext ((MulChar.coe_toUnitHom χ u).trans ((mem_ann Ξ u).mp hu χ hχ))

def theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : (frame Ξ e hev).Char :=
  (thetaB Ξ χ hχ).comp
    ((data Ξ e hev).xiA.comp (MonoidHom.snd G0 (data Ξ e hev).frame.MA))

theorem theta_mem (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : theta Ξ e hev χ hχ ∈ (frame Ξ e hev).Chat := by
  simp only [Frame.Chat, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · unfold Frame.TrivialOnFirstFactor
    intro s hs
    have h1 := ((data Ξ e hev).mem_cusp_forms_iff_automorphic_compact s).mp hs
    show thetaB Ξ χ hχ ((data Ξ e hev).xiA ((data Ξ e hev).frame.iota s)) = 1
    rw [h1]
    exact map_one (thetaB Ξ χ hχ)
  · show thetaB Ξ χ hχ ((data Ξ e hev).xiA 1) = 1
    rw [map_one]
    exact map_one (thetaB Ξ χ hχ)
  · show thetaB Ξ χ hχ ((data Ξ e hev).xiA 1) = 1
    rw [map_one]
    exact map_one (thetaB Ξ χ hχ)

theorem theta_toA (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) (s : G0) (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) :
    theta Ξ e hev χ hχ (s, (data Ξ e hev).toA (ZMod.unitsMap (QS_dvd Ξ e) u)) =
      χ.toUnitHom (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u) := by
  show thetaB Ξ χ hχ ((data Ξ e hev).xiA ((data Ξ e hev).toA (ZMod.unitsMap (QS_dvd Ξ e) u))) = _
  have h1 : (data Ξ e hev).xiA ((data Ξ e hev).toA (ZMod.unitsMap (QS_dvd Ξ e) u)) = xiW Ξ e u :=
    ((data Ξ e hev).xiA_toA (ZMod.unitsMap (QS_dvd Ξ e) u)).trans (xi_unitsMap Ξ e u)
  rw [h1]
  rfl

theorem exists_theta (θ : (frame Ξ e hev).Char) (hθ : θ ∈ (frame Ξ e hev).Chat) : ∃ χ hχ, theta Ξ e hev χ hχ = θ := by
  obtain ⟨h1, h2, h3⟩ := hθ
  set D := data Ξ e hev with hD
  have hsurj : Function.Surjective D.xiA := fun b => by
    obtain ⟨u, rfl⟩ := xi_surj Ξ e b
    exact ⟨D.toA u, D.xiA_toA u⟩
  let θA : D.frame.MA →* ℂˣ := θ.comp (MonoidHom.inr G0 D.frame.MA)
  let θB : B Ξ →* ℂˣ := D.xiA.liftOfSurjective hsurj ⟨θA, fun a ha => h1 a.toAdd ((D.mem_cusp_forms_iff_automorphic_compact a.toAdd).mpr ha)⟩
  have hB : ∀ a, θB (D.xiA a) = θA a := fun a => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a
  have hχ : MulChar.ofUnitHom (θB.comp (QuotientGroup.mk' _)) ∈ Ξ := by
    refine (mem_iff Ξ _).mpr fun u hu => ?_
    rw [MulChar.ofUnitHom_coe, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).mpr hu, map_one,
      Units.val_one]
  have h0 : ∀ s : G0, θ (s, 1) = 1 := by
    rintro ⟨s, t⟩
    have h4 : θ (frame Ξ e hev).sg = 1 := by rw [← Frame.cc_mul_iod, map_mul, h2, h3, one_mul]
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
    · exact map_one θ
    · exact h2
    · exact h4
    · exact h3
  refine ⟨_, hχ, MonoidHom.ext fun g => ?_⟩
  obtain ⟨s, a⟩ := g
  obtain ⟨v, rfl⟩ := D.toA_surj a
  obtain ⟨u, rfl⟩ := ZMod.unitsMap_surjective (QS_dvd Ξ e) v
  refine (theta_toA Ξ e hev _ hχ s u).trans (Units.ext ?_)
  have h5 : θ (s, D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) = θA (D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) := by
    have h6 : ((s, D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) : (frame Ξ e hev).GG) =
        (s, 1) * (1, D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) := Prod.ext (mul_one _).symm (one_mul _).symm
    exact (congrArg θ h6).trans ((map_mul θ _ _).trans ((congrArg (· * _) (h0 s)).trans (one_mul _)))
  rw [MulChar.coe_toUnitHom, MulChar.ofUnitHom_coe]
  refine congrArg Units.val (Eq.trans ?_ h5.symm)
  exact (congrArg θB ((D.xiA_toA _).trans (xi_unitsMap Ξ e u))).symm.trans (hB _)

section Host

variable {q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) (he : 2 ≤ e)
  (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1)

include hH hc in
theorem coprime_QS : Nat.Coprime (QS Ξ e) (q * d) := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := hH
  have h2 : Nat.Coprime 2 (q * d) := by
    rw [Nat.coprime_mul_iff_right]
    constructor
    · exact (Nat.coprime_primes Nat.prime_two hq).mpr (by omega)
    · exact (Nat.coprime_primes Nat.prime_two hd).mpr (by omega)
  exact Nat.Coprime.coprime_dvd_left (QS_dvd_mul Ξ e) (Nat.Coprime.mul (Nat.Coprime.pow_left _ h2) hc)

def host : HostRaw (frame Ξ e hev) :=
  (data Ξ e hev).host hH (coprime_QS Ξ e hH hc) he fun l hl h2 h => hs l hl h2 (dvd_of_dvd_QS Ξ e hl h2 h)

theorem host_q : (host Ξ e hev hH hc he hs).q = q := rfl
theorem host_d : (host Ξ e hev hH hc he hs).d = d := rfl
theorem host_QS : (host Ξ e hev hH hc he hs).QS = QS Ξ e := rfl

theorem psQ : (host Ξ e hev hH hc he hs).PsQ := by
  apply (data Ξ e hev).psQ

theorem exact : (host Ξ e hev hH hc he hs).Exact := by
  apply (data Ξ e hev).exact
  intro l hl hd
  exact exact_data Ξ e hev (by omega) l hl hd

theorem muPM (hq : q ≠ 3) : (host Ξ e hev hH hc he hs).MuPM := by
  apply (data Ξ e hev).muPM
  exact hq

theorem coprimeFifteen_of_coprime (h : Nat.Coprime M 15) : (host Ξ e hev hH hc he hs).CoprimeFifteen := by
  show Nat.Coprime (QS Ξ e) 15
  exact Nat.Coprime.coprime_dvd_left (QS_dvd_mul Ξ e) (Nat.Coprime.mul (Nat.Coprime.pow_left _ (by decide)) h)

theorem exists_sqq : ∃ s : (host Ξ e hev hH hc he hs).E, s ^ 2 = -((host Ξ e hev hH hc he hs).q : (host Ξ e hev hH hc he hs).E) ∧
    ∀ σ : (host Ξ e hev hH hc he hs).E ≃ₐ[ℚ] (host Ξ e hev hH hc he hs).E,
      σ s = (((((host Ξ e hev hH hc he hs).gal σ).1.1 : ℤˣ) : ℤ) : (host Ξ e hev hH hc he hs).E) * s := by
  apply (data Ξ e hev).exists_sqq

theorem prim_theta (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) :
    PChar.of χ = (host Ξ e hev hH hc he hs).prim (theta Ξ e hev χ hχ) := by
  set H := host Ξ e hev hH hc he hs with hHdef
  refine An.Induces.unique (f := fun a => χ (a : ZMod M)) (M := H.condN * M) (mul_ne_zero H.condN_pos.ne' (NeZero.ne M))
    ⟨(PChar.of χ).prim, fun a ha => (An.induces_of χ).2 a ha.coprime_mul_left_right⟩ ⟨(H.prim _).prim, fun a ha => ?_⟩
  have haN : a.Coprime H.condN := ha.coprime_mul_right_right
  have haM : a.Coprime M := ha.coprime_mul_left_right
  have haW : a.Coprime (Nat.lcm (2 ^ (e + 2)) M) :=
    (Nat.Coprime.mul_right (haN.coprime_dvd_right ((H.tower_dvd.mul_right _).mul_right _)) haM).coprime_dvd_right
      (Nat.lcm_dvd_mul _ _)
  refine ((H.isPrimOf_prim _).2 a haN).trans ?_
  show _ = χ (a : ZMod M)
  rw [HostRaw.dirAt, ← ZMod.coe_unitOfCoprime a haN, H.dir_unit, ← ZMod.coe_unitOfCoprime a haM, ← MulChar.coe_toUnitHom]
  refine congrArg Units.val ?_
  have h1 := theta_toA Ξ e hev χ hχ (H.art (ZMod.unitOfCoprime a haN)).1 (ZMod.unitOfCoprime a haW)
  rw [unitsMap_unitOfCoprime, unitsMap_unitOfCoprime] at h1
  have h2 : (H.art (ZMod.unitOfCoprime a haN)).2 =
      (data Ξ e hev).toA (ZMod.unitOfCoprime a (haW.coprime_dvd_right (QS_dvd Ξ e))) :=
    congrArg (data Ξ e hev).toA (unitsMap_unitOfCoprime ((data Ξ e hev).m_dvd q d) a haN)
  have h3 : H.art (ZMod.unitOfCoprime a haN) = ((H.art (ZMod.unitOfCoprime a haN)).1,
      (data Ξ e hev).toA (ZMod.unitOfCoprime a (haW.coprime_dvd_right (QS_dvd Ξ e)))) := Prod.ext rfl h2
  exact (congrArg (theta Ξ e hev χ hχ) h3).trans h1

theorem keptEqChat : (host Ξ e hev hH hc he hs).KeptEqChat (Level.ofSub Ξ).KEPT := by
  unfold HostRaw.KeptEqChat HostRaw.Kept
  refine ⟨fun ψ hψ => ?_, fun θ hθ => ?_⟩
  · obtain ⟨χ, hχ, rfl⟩ := (Level.mem_ofSub Ξ ψ).mp hψ
    exact ⟨theta Ξ e hev χ hχ, theta_mem Ξ e hev χ hχ,
      ((host Ξ e hev hH hc he hs).isPrimOf_iff _ _).mpr (prim_theta Ξ e hev hH hc he hs χ hχ)⟩
  · obtain ⟨χ, hχ, rfl⟩ := exists_theta Ξ e hev θ hθ
    exact ⟨PChar.of χ, (Level.mem_ofSub Ξ _).mpr ⟨χ, hχ, rfl⟩,
      ((host Ξ e hev hH hc he hs).isPrimOf_iff _ _).mpr (prim_theta Ξ e hev hH hc he hs χ hχ)⟩

theorem keptInXp : (host Ξ e hev hH hc he hs).KeptInXp (Level.ofSub Ξ).KEPT := by
  have hk := keptEqChat Ξ e hev hH hc he hs
  unfold HostRaw.KeptEqChat at hk
  unfold HostRaw.KeptInXp
  intro ψ hψ
  obtain ⟨θ, hθ, h⟩ := hk.1 ψ hψ
  refine ⟨θ, ?_, h⟩
  simp only [Frame.Chat, Frame.Xp, Set.mem_setOf_eq] at hθ ⊢
  exact ⟨hθ.1, hθ.2.1⟩

theorem exceptional_character_condition : (host Ξ e hev hH hc he hs).ExceptionalCharacterKept (Level.ofSub Ξ).KEPT (Level.ofSub Ξ).psK := by
  refine ⟨fun ψ h => (by cases h), fun _ h => ?_⟩
  obtain ⟨χ, hχ, h1⟩ := (Level.mem_ofSub Ξ _).mp ((HostRaw.kept_iff _ _ _).mp h)
  rw [prim_theta Ξ e hev hH hc he hs χ hχ] at h1
  have h2 := HostRaw.art_eq_of_prim_eq _ h1 (-1)
  rw [HostRaw.art_neg_one, (theta_mem Ξ e hev χ hχ).2.2] at h2
  have h3 : (1 : ℂ) = ((-1 : ℤ) : ℂ) := congrArg Units.val h2
  norm_num at h3

theorem o_eq_level : (frame Ξ e hev).o = (Level.ofSub Ξ).o := o_eq Ξ e hev

end Host

end EvenGrp

end Formalism.HC

end

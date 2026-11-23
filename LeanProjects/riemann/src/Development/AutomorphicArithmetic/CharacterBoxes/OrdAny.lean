import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.AnyLevel

open Formalism.HC Formalism.FrobeniusOrbits UpperTheory.Top

private theorem ord_eq_mul (D : ModData) : D.frame.ord = Nat.card (D.cl.ker.map D.ξ) * 2 ^ D.e := by
  rw [D.ord_eq, ← Group.card_H D.e]
  have hk : Nat.card D.R = Nat.card D.p1.ker * Nat.card (HGrp D.e) := by
    rw [← Subgroup.card_mul_index D.p1.ker, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr D.projection_surjective, Subgroup.card_top]
  rw [hk]
  congr 1
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨(x.1 : HGrp D.e × D.B).2, ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨⟨y, u, hu⟩, hx⟩ := x
    have h1 : y.1 = 1 := hx
    refine ⟨u, ?_, ?_⟩
    · change D.cl u = 1
      rw [← h1, ← hu]
      rfl
    · exact congrArg Prod.snd hu
  · rintro ⟨⟨x, hx⟩, hx1⟩ ⟨⟨y, hy⟩, hy1⟩ h
    have a1 : x.1 = 1 := hx1
    have b1 : y.1 = 1 := hy1
    have h2 : x.2 = y.2 := congrArg Subtype.val h
    ext1
    ext1
    exact Prod.ext (a1.trans b1.symm) h2
  · rintro ⟨b, u, hu, rfl⟩
    refine ⟨⟨⟨D.eta u, u, rfl⟩, ?_⟩, rfl⟩
    exact hu

private theorem cl_eq_one_iff (D : ModData) (u : (ZMod D.m)ˣ) :
    D.cl u = 1 ↔ ZMod.unitsMap D.tower u = 1 ∨ ZMod.unitsMap D.tower u = -1 := by
  change (QuotientGroup.mk' _ (ZMod.unitsMap D.tower u) : HGrp D.e) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]
    rcases Int.even_or_odd k with hk2 | hk2
    · exact Or.inl hk2.neg_one_zpow
    · exact Or.inr hk2.neg_one_zpow
  · rintro (h | h)
    · exact ⟨0, by rw [h, zpow_zero]⟩
    · exact ⟨1, by rw [h, zpow_one]⟩

private theorem unitsMap_unitsMap {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (u : (ZMod c)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 u) = ZMod.unitsMap (h1.trans h2) u := by
  rw [← ZMod.unitsMap_comp h1 h2]
  rfl

private theorem step {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) (b : EvenGrp.B Ξ)
    (hb : b ∈ (AnyGrp.data Ξ (e + 1)).cl.ker.map (AnyGrp.data Ξ (e + 1)).ξ) :
    b ∈ (AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ := by
  obtain ⟨u, hu, rfl⟩ := hb
  have hL : (2 ^ (e + 2)).lcm M ∣ (2 ^ (e + 1 + 2)).lcm M :=
    Nat.lcm_dvd (dvd_trans (pow_dvd_pow 2 (by omega)) (Nat.dvd_lcm_left _ _)) (Nat.dvd_lcm_right _ _)
  haveI : NeZero ((2 ^ (e + 1 + 2)).lcm M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩
  obtain ⟨w, rfl⟩ := ZMod.unitsMap_surjective (EvenGrp.QS_dvd Ξ (e + 1)) u
  have h23 : 2 ^ (e + 2) ∣ 2 ^ (e + 1 + 2) := pow_dvd_pow 2 (by omega)
  have t0 : 2 ^ (e + 2) ∣ EvenGrp.QS Ξ e := (AnyGrp.data Ξ e).tower
  have t1 : 2 ^ (e + 1 + 2) ∣ EvenGrp.QS Ξ (e + 1) := (AnyGrp.data Ξ (e + 1)).tower
  refine ⟨ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hL w), ?_, ?_⟩
  · have hu' := (cl_eq_one_iff (AnyGrp.data Ξ (e + 1)) (ZMod.unitsMap (EvenGrp.QS_dvd Ξ (e + 1)) w)).mp hu
    refine (cl_eq_one_iff (AnyGrp.data Ξ e) (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hL w))).mpr ?_
    change ZMod.unitsMap t0 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hL w)) = 1 ∨
      ZMod.unitsMap t0 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hL w)) = -1
    change ZMod.unitsMap t1 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ (e + 1)) w) = 1 ∨
      ZMod.unitsMap t1 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ (e + 1)) w) = -1 at hu'
    rw [unitsMap_unitsMap, unitsMap_unitsMap]
    rw [unitsMap_unitsMap] at hu'
    rcases hu' with h | h
    · left
      have := congrArg (ZMod.unitsMap h23) h
      rw [unitsMap_unitsMap, map_one] at this
      exact this
    · right
      have := congrArg (ZMod.unitsMap h23) h
      rw [unitsMap_unitsMap, D7.unitsMap_neg_one] at this
      exact this
  · change EvenGrp.xi Ξ e _ = EvenGrp.xi Ξ (e + 1) _
    rw [EvenGrp.xi_unitsMap, EvenGrp.xi_unitsMap]
    change QuotientGroup.mk' _ (ZMod.unitsMap _ (ZMod.unitsMap hL w)) = QuotientGroup.mk' _ (ZMod.unitsMap _ w)
    rw [unitsMap_unitsMap]

theorem UpperTheory.Top.ordAny :
    ∀ (M : ℕ) [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)), ∃ c e0 : ℕ, 1 ≤ c ∧ c ≤ Nat.card Ξ ∧
      ∀ e ≥ e0, (AnyGrp.frame Ξ e).ord = c * 2 ^ e := by
  intro M _ Ξ
  haveI hB : Finite (EvenGrp.B Ξ) :=
    Nat.finite_of_card_ne_zero (by rw [EvenGrp.card_B]; exact Nat.card_pos.ne')
  haveI : ∀ e, Finite (AnyGrp.data Ξ e).B := fun _ => hB
  let n : ℕ → ℕ := fun e => Nat.card ((AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ)
  have hanti : Antitone n :=
    antitone_nat_of_succ_le (fun e => Subgroup.card_le_of_le (fun b hb => step Ξ e b hb))
  have hpos : ∀ e, 1 ≤ n e := fun e => Nat.card_pos
  have hle : ∀ e, n e ≤ Nat.card Ξ := fun e => by
    rw [← EvenGrp.card_B]
    exact Subgroup.card_le_card_group _
  obtain ⟨e0, he0⟩ : sInf (Set.range n) ∈ Set.range n := Nat.sInf_mem (Set.range_nonempty n)
  refine ⟨n e0, e0, hpos e0, hle e0, fun e he => ?_⟩
  change (AnyGrp.data Ξ e).frame.ord = _
  rw [ord_eq_mul]
  have h1 : n e ≤ n e0 := hanti he
  have h2 : n e0 ≤ n e := he0 ▸ Nat.sInf_le ⟨e, rfl⟩
  have h3 : n e = n e0 := le_antisymm h1 h2
  exact congrArg (· * 2 ^ e) h3

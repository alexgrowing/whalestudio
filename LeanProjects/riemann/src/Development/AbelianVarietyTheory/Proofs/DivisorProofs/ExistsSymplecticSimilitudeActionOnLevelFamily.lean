import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapCompBis

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.SympAct

theorem exists_smul_iff {h : ℕ} (M : ℕ) (w : Fin h ⊕ Fin h → ℤ) : (∃ c, w = M • c) ↔ reduceMod M w = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    funext i
    simp [reduceMod]
  · intro hw
    refine ⟨fun i => w i / M, ?_⟩
    funext i
    have hd : (M : ℤ) ∣ w i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun hw i)
    simp only [Pi.smul_apply, nsmul_eq_mul]
    rw [Int.mul_ediv_cancel' hd]

theorem lev_eq_of_reduce {h : ℕ} {T : Type*} [Monoid T] {M : ℕ} (hM : 0 < M) (lev : (Fin h ⊕ Fin h → ℤ) → T)
    (hadd : ∀ a b, lev (a + b) = lev a * lev b) (htor : ∀ a, lev a ^ M = 1) {x y : Fin h ⊕ Fin h → ℤ}
    (hxy : reduceMod M x = reduceMod M y) : lev x = lev y := by
  have hsm : ∀ (n : ℕ) c, lev ((n + 1) • c) = lev c ^ (n + 1) := by
    intro n c
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, hadd, ih, ← pow_succ]
  obtain ⟨c, hc⟩ := (exists_smul_iff M (x - y)).2 (by
    funext i
    have e := congrFun hxy i
    simp only [reduceMod] at e
    simp only [reduceMod, Pi.sub_apply, Int.cast_sub, e, sub_self, Pi.zero_apply])
  have hx : x = y + M • c := by rw [← hc]; abel
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  rw [hx, hadd, hsm, htor, _root_.mul_one]

theorem omegaStd_cast {h : ℕ} (M : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    ((omegaStd a b : ℤ) : ZMod M) = omegaMod M (reduceMod M a) (reduceMod M b) := by
  simp [omegaStd, omegaMod, reduceMod]

theorem zpow_eq_of_cast_eq {G : Type*} [Group G] {M : ℕ} (z : G) (hz : z ^ M = 1) {k l : ℤ}
    (hkl : (k : ZMod M) = l) : z ^ k = z ^ l := by
  obtain ⟨t, ht⟩ : (M : ℤ) ∣ k - l := (ZMod.intCast_eq_intCast_iff_dvd_sub l k M).1 hkl.symm
  have e : k = l + M * t := by linarith
  rw [e, zpow_add, zpow_mul, zpow_natCast, hz, one_zpow, _root_.mul_one]

theorem pow_eq_of_cast_eq {G : Type*} [Monoid G] {M : ℕ} (z : G) (hz : z ^ M = 1) {k l : ℕ}
    (hkl : (k : ZMod M) = l) : z ^ k = z ^ l := by
  rw [ZMod.natCast_eq_natCast_iff'] at hkl
  rw [← Nat.div_add_mod k M, ← Nat.div_add_mod l M, hkl, pow_add, pow_add, pow_mul, pow_mul, hz, one_pow, one_pow]

theorem mult_unique {h M : ℕ} (hh : 0 < h) (g : sympSimGrp h M) {n n' : ℕ} (hn : IsMultOf g n)
    (hn' : IsMultOf g n') : (n : ZMod M) = n' := by
  classical
  let e : Fin h ⊕ Fin h → ZMod M := Pi.single (Sum.inl ⟨0, hh⟩) 1
  let f : Fin h ⊕ Fin h → ZMod M := Pi.single (Sum.inr ⟨0, hh⟩) 1
  have hef : omegaMod M e f = 1 := by
    simp [omegaMod, e, f, Pi.single_apply]
  have := (hn e f).symm.trans (hn' e f)
  rw [hef] at this
  simpa using this

theorem isMultOf_mul {h M : ℕ} {a c : sympSimGrp h M} {n n' : ℕ} (ha : IsMultOf a n) (hc : IsMultOf c n') :
    IsMultOf (a * c) (n * n') := by
  intro x y
  change omegaMod M ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
    ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) x))
    ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
    ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) y)) = _
  rw [ha, hc]
  push_cast
  ring

theorem isMultOf_one {h M : ℕ} : IsMultOf (1 : sympSimGrp h M) 1 := by
  intro x y
  change omegaMod M x y = ((1 : ℕ) : ZMod M) * omegaMod M x y
  simp

theorem exists_mult {h M : ℕ} [NeZero M] (a : sympSimGrp h M) :
    ∃ n : ℕ, IsMultOf a n ∧ n.Coprime M ∧ (h = 0 → n = 1) := by
  by_cases hh : h = 0
  · subst hh
    exact ⟨1, fun x y => by simp [omegaMod], Nat.coprime_one_left _, fun _ => rfl⟩
  · obtain ⟨m, hm⟩ := a.2
    exact ⟨(m : ZMod M).val, fun x y => by rw [ZMod.natCast_zmod_val]; exact hm x y,
      ZMod.val_coe_unit_coprime m, fun h0 => absurd h0 hh⟩

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def idObjMap {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) : ObjMap o o (𝟙 S) :=
  { φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
    act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }

theorem isSympLev_twist {b : Base D R} {N h M : ℕ} (hM : 0 < M) {X : Scheme.{0}} {s : X ⟶ Sp R}
    {s₁ : X ⟶ Sp (cycAway M)} (u : Obj b N s) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A))
    (hlev : IsSympLev u.P h M (zetaAway M) s₁ lev) (a : sympSimGrp h M) (n : ℕ) (ha : IsMultOf a n)
    (σ : cycAway M →+* cycAway M) (hσ : σ (zetaAway M) = zetaAway M ^ n) :
    IsSympLev u.P h M (zetaAway M) (s₁ ≫ spMap σ) (sympTwist a lev) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, htor, hgeo⟩ := hlev
  have hres : ∀ {x y : Fin h ⊕ Fin h → ℤ}, reduceMod M x = reduceMod M y → lev x = lev y :=
    fun hxy => lev_eq_of_reduce hM lev hadd htor hxy
  have hred_add : ∀ x y : Fin h ⊕ Fin h → ℤ, reduceMod M (x + y) = reduceMod M x + reduceMod M y := by
    intro x y; funext i; simp [reduceMod]
  refine ⟨fun x y => ?_, fun x => htor _, ?_⟩
  · simp only [sympTwist]
    rw [← hadd]
    apply hres
    simp only [hred_add, reduceMod_liftMod, map_add]
  · intro k _ _ x β z hx hz
    obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : cycAway M →+* k, x ≫ s₁ = spMap β₀ :=
      ⟨(Spec.preimage (x ≫ s₁)).hom, by simp [spMap]⟩
    have hββ : β = β₀.comp σ := by
      have e : spMap β = spMap (β₀.comp σ) := by
        rw [← hx, ← Category.assoc, hβ₀, spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 e)
    have hζ := isPrimitiveRoot_zetaAway hM.ne'
    let z₀ : kˣ := ((hζ.isUnit hM.ne').map β₀).unit
    have hz₀ : (z₀ : k) = β₀ (zetaAway M) := IsUnit.unit_spec _
    have hz' : z = z₀ ^ n := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hz, hββ, RingHom.comp_apply, hσ, map_pow, hz₀]
    have hz₀M : z₀ ^ M = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hz₀, ← map_pow, hζ.pow_eq_one, map_one, Units.val_one]
    obtain ⟨hker, hsurj, hweil⟩ := hgeo k x β₀ z₀ hβ₀ hz₀
    refine ⟨fun w => ?_, fun g hg => ?_, fun w v => ?_⟩
    · simp only [sympTwist]
      rw [hker, exists_smul_iff, exists_smul_iff, reduceMod_liftMod]
      exact LinearEquiv.map_eq_zero_iff _
    · obtain ⟨w, hw⟩ := hsurj g hg
      refine ⟨liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)).symm (reduceMod M w)), ?_⟩
      simp only [sympTwist]
      rw [reduceMod_liftMod, LinearEquiv.apply_symm_apply, ← hw]
      congr 1
      exact hres (reduceMod_liftMod _)
    · simp only [sympTwist]
      have key : z ^ (2 * omegaStd w v) = z₀ ^ (2 * omegaStd
          (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M w)))
          (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M v)))) := by
        rw [hz', ← zpow_natCast, ← zpow_mul]
        apply zpow_eq_of_cast_eq z₀ hz₀M
        push_cast
        rw [omegaStd_cast, omegaStd_cast, reduceMod_liftMod, reduceMod_liftMod, ha]
        ring
      rw [key]
      exact hweil _ _

theorem exists_sympActs : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∃ ρ : sympSimGrp h M → (X ⟶ X), ρ 1 = 𝟙 X ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ SympActs s s₁ u lev ρ := by
  intro p _ D R _ b N h M hM X s s₁ u lev hlev huniv
  haveI : NeZero M := ⟨hM.ne'⟩
  have hζ := isPrimitiveRoot_zetaAway hM.ne'
  have hζM : zetaAway M ^ M = 1 := hζ.pow_eq_one
  have hadd := hlev.1
  have htor := hlev.2.1
  have hres : ∀ {x y : Fin h ⊕ Fin h → ℤ}, reduceMod M x = reduceMod M y → lev x = lev y :=
    fun hxy => lev_eq_of_reduce hM lev hadd htor hxy
  choose n hn hcop h0 using fun a : sympSimGrp h M => exists_mult a
  have hσex : ∀ a, ∃ σ : cycAway M →+* cycAway M, σ (zetaAway M) = zetaAway M ^ n a := fun a =>
    let ⟨σ, hσ⟩ := exists_cycAway_aut hM.ne' (hcop a); ⟨σ.toRingHom, hσ⟩
  choose σ hσ using hσex
  have hU : ∀ a, ∃! f : X ⟶ X, f ≫ s = s ∧ f ≫ s₁ = s₁ ≫ spMap (σ a) ∧
      ∃ m : ObjMap u u f, ∀ x, (sympTwist a lev x).left ≫ m.φ = f ≫ (lev x).left :=
    fun a => huniv X s (s₁ ≫ spMap (σ a)) u (sympTwist a lev)
      (isSympLev_twist hM u lev hlev a (n a) (hn a) (σ a) (hσ a))
  choose ρ hρ hρu using hU
  have hcons : ∀ a c, zetaAway M ^ n (a * c) = zetaAway M ^ (n a * n c) := by
    intro a c
    by_cases hh : h = 0
    · rw [h0 _ hh, h0 _ hh, h0 _ hh]
    · exact pow_eq_of_cast_eq _ hζM (mult_unique (Nat.pos_of_ne_zero hh) _ (hn _) (isMultOf_mul (hn a) (hn c)))
  have hone : zetaAway M ^ n 1 = zetaAway M := by
    by_cases hh : h = 0
    · rw [h0 _ hh, pow_one]
    · rw [pow_eq_of_cast_eq _ hζM (mult_unique (Nat.pos_of_ne_zero hh) _ (hn 1) isMultOf_one), pow_one]
  refine ⟨ρ, ?_, fun a c => ?_, fun a => ⟨(hρ a).1, ⟨n a, σ a, hn a, hσ a, (hρ a).2.1⟩, (hρ a).2.2⟩⟩
  · have hσ1 : σ 1 = RingHom.id _ := cycAway_hom_ext hM.ne' (by rw [hσ, hone]; rfl)
    refine (hρu 1 (𝟙 X) ⟨Category.id_comp _, ?_, ?_⟩).symm
    · rw [hσ1, Category.id_comp]
      simp [spMap]
    · refine ⟨idObjMap u, fun x => ?_⟩
      change (lev (liftMod (reduceMod M x))).left ≫ 𝟙 _ = 𝟙 X ≫ (lev x).left
      rw [Category.comp_id, Category.id_comp, hres (reduceMod_liftMod _)]
  · have hσmul : σ (a * c) = (σ a).comp (σ c) := cycAway_hom_ext hM.ne' (by
      rw [hσ, RingHom.comp_apply, hσ, map_pow, hσ, ← pow_mul, hcons])
    refine (hρu (a * c) (ρ a ≫ ρ c) ⟨?_, ?_, ?_⟩).symm
    · rw [Category.assoc, (hρ c).1, (hρ a).1]
    · rw [Category.assoc, (hρ c).2.1, ← Category.assoc, (hρ a).2.1, Category.assoc, hσmul, spMap, spMap, spMap,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · obtain ⟨ma, hma⟩ := (hρ a).2.2
      obtain ⟨mc, hmc⟩ := (hρ c).2.2
      refine ⟨ObjMapComp.comp ma mc, fun x => ?_⟩
      change (sympTwist (a * c) lev x).left ≫ ma.φ ≫ mc.φ = (ρ a ≫ ρ c) ≫ (lev x).left
      have e1 : sympTwist (a * c) lev x = sympTwist a lev
          (liftMod ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x))) := by
        simp only [sympTwist, reduceMod_liftMod]
        rfl
      rw [e1, ← Category.assoc, hma, Category.assoc]
      change ρ a ≫ (sympTwist c lev x).left ≫ mc.φ = _
      rw [hmc, Category.assoc]

end GlobalTheory.UPel.HT.SympAct

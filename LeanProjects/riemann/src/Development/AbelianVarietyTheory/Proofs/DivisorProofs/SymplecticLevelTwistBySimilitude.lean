import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

theorem reduceMod_eq_zero_iff {h : ℕ} (M : ℕ) (u : Fin h ⊕ Fin h → ℤ) :
    reduceMod M u = 0 ↔ ∃ c, u = M • c := by
  constructor
  · intro hu
    refine ⟨fun i => u i / M, ?_⟩
    funext i
    have hi : ((u i : ℤ) : ZMod M) = 0 := congrFun hu i
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hi
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' hi).symm
  · rintro ⟨c, rfl⟩
    funext i
    simp [reduceMod]

theorem omegaStd_cast {h : ℕ} (M : ℕ) (u v : Fin h ⊕ Fin h → ℤ) :
    ((omegaStd u v : ℤ) : ZMod M) = omegaMod M (reduceMod M u) (reduceMod M v) := by
  simp [omegaStd, omegaMod, reduceMod]

theorem sympCond_twist : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
    (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)), SympCond o h M T t₁ lv →
    ∀ (a : sympSimGrp h M) (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n →
      σ (zetaAway M) = zetaAway M ^ n → SympCond o h M T (t₁ ≫ spMap σ) (sympTwist a lv) := by
  intro p _ D R _ b N h M hM S t o T t₁ lv hlv a n σ hn hσ
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, htor, hgeo⟩ := hlv

  let φ : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (T ⟶ o.A) :=
    MonoidHom.mk' (fun u => lv (Multiplicative.toAdd u)) (fun u v => hadd _ _)
  have hsm : ∀ (k : ℕ) (w : Fin h ⊕ Fin h → ℤ), lv (k • w) = lv w ^ k := by
    intro k w
    have := map_pow φ (Multiplicative.ofAdd w) k
    simpa [φ, ← ofAdd_nsmul] using this
  have per : ∀ {u v : Fin h ⊕ Fin h → ℤ}, reduceMod M u = reduceMod M v → lv u = lv v := by
    intro u v huv
    have h0 : reduceMod M (u - v) = 0 := by
      funext i
      have := congrFun huv i
      simp only [reduceMod, Pi.sub_apply, Pi.zero_apply, Int.cast_sub] at this ⊢
      rw [this, sub_self]
    obtain ⟨w, hw⟩ := (reduceMod_eq_zero_iff M _).1 h0
    have : u = v + M • w := by rw [← hw]; abel
    rw [this, hadd, hsm, htor, _root_.mul_one]
  let g := (a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
  have tw : ∀ u, sympTwist a lv u = lv (liftMod (g (reduceMod M u))) := fun u => rfl
  have redAdd : ∀ u v : Fin h ⊕ Fin h → ℤ, reduceMod M (u + v) = reduceMod M u + reduceMod M v := by
    intro u v; funext i; simp [reduceMod]
  refine ⟨fun u c => ?_, fun u => ?_, fun k _ _ x β' z' hx' hz' => ?_⟩
  · rw [tw, tw, tw, ← hadd]
    apply per
    rw [reduceMod_liftMod, redAdd, redAdd, reduceMod_liftMod, reduceMod_liftMod, map_add]
  · rw [tw]; exact htor _
  ·
    set β : cycAway M →+* k := (Spec.preimage (x ≫ t₁)).hom with hβdef
    have hβ : x ≫ t₁ = spMap β := by
      simp only [spMap, hβdef, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hβ' : β' = β.comp σ := by
      have e : spMap β' = spMap (β.comp σ) := by
        rw [spMap_comp, ← hx', ← hβ, Category.assoc]
      have := Spec.map_injective e
      exact congrArg CommRingCat.Hom.hom this
    have hζM : β (zetaAway M) ^ M = 1 := by
      rw [← map_pow, zetaAway_pow_self M hM.ne', map_one]
    have hne : β (zetaAway M) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM.ne'] at hζM
      exact zero_ne_one hζM
    set z : kˣ := Units.mk0 (β (zetaAway M)) hne with hzdef
    have hz : (z : k) = β (zetaAway M) := rfl
    have hzz : z' = z ^ n := by
      ext
      rw [hz', hβ', RingHom.comp_apply, hσ, map_pow, Units.val_pow_eq_pow_val, hz]
    have hzM : z ^ (M : ℤ) = 1 := by
      rw [zpow_natCast]; ext; rw [Units.val_pow_eq_pow_val, hz, hζM]; rfl
    obtain ⟨hK, hS, hW⟩ := hgeo k x β z hβ hz
    refine ⟨fun u => ?_, fun g' hg' => ?_, fun u c => ?_⟩
    · rw [tw, hK]
      constructor
      · rintro ⟨c, hc⟩
        apply (reduceMod_eq_zero_iff M u).1
        have : g (reduceMod M u) = 0 := by
          rw [← reduceMod_liftMod (g (reduceMod M u)), hc]
          exact (reduceMod_eq_zero_iff M _).2 ⟨c, rfl⟩
        exact (LinearEquiv.map_eq_zero_iff _).1 this
      · intro hu
        apply (reduceMod_eq_zero_iff M _).1
        rw [reduceMod_liftMod, (reduceMod_eq_zero_iff M u).2 hu, map_zero]
    · obtain ⟨u₀, hu₀⟩ := hS g' hg'
      refine ⟨liftMod (g.symm (reduceMod M u₀)), ?_⟩
      rw [tw, reduceMod_liftMod, LinearEquiv.apply_symm_apply, per (reduceMod_liftMod _)]
      exact hu₀
    · rw [tw, tw]
      set u' := liftMod (g (reduceMod M u))
      set c' := liftMod (g (reduceMod M c))
      have hcast : ((2 * omegaStd u' c' : ℤ) : ZMod M) = (((n : ℤ) * (2 * omegaStd u c) : ℤ) : ZMod M) := by
        push_cast
        rw [omegaStd_cast, omegaStd_cast, reduceMod_liftMod, reduceMod_liftMod]
        rw [show omegaMod M (g (reduceMod M u)) (g (reduceMod M c)) = n * omegaMod M (reduceMod M u) (reduceMod M c)
          from hn _ _]
        ring
      have e : z' ^ (2 * omegaStd u c) = z ^ (2 * omegaStd u' c') := by
        rw [hzz, ← zpow_natCast z, ← zpow_mul, zpow_eq_zpow_emod _ hzM, zpow_eq_zpow_emod (2 * omegaStd u' c') hzM]
        congr 1
        exact ((ZMod.intCast_eq_intCast_iff' _ _ _).1 hcast).symm
      rw [e]
      exact hW u' c'

end GlobalTheory.HTSympCover

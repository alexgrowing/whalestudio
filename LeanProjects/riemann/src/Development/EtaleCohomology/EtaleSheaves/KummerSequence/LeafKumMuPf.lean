import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumSeqPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.H2CurveOrder.LeafKumMuPf

variable {R : Type} [CommRing R]

abbrev evU (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

theorem kerSec_inj {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) :
    Function.Injective (Sec.map (kernel.ι φ) (U := U)) := by
  have hm : Mono ((evU U).map (kernel.ι φ)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 hm

theorem secMap_comp {F G K : Shv R} (f : F ⟶ G) (g : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem secMap_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

def LeafKumMuUnits : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, κ ≫ LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q = 0 ∧
    ∀ U : Scheme.{0}, Nonempty (Sx (sp B) 0 U) → Function.Injective (Sec.map κ (U := U)) ∧
      ∀ s : Sec Gm U, Sec.map (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q) s = 0 → ∃ t, Sec.map κ t = s

def LeafKumMuSec : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ kernel (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q),
    ∀ U : Scheme.{0}, Nonempty (Sx (sp B) 0 U) → Function.Bijective (Sec.map κ (U := U))

theorem LeafKumMuSec_of (hU : LeafKumMuUnits) : LeafKumMuSec := by
  intro q _ B _ hq
  obtain ⟨κ, h0, hκ⟩ := hU q B hq
  refine ⟨kernel.lift _ κ h0, fun U hUB => ?_⟩
  obtain ⟨hi, hs⟩ := hκ U hUB
  have hc : ∀ t : Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U, Sec.map (kernel.ι _) (Sec.map (kernel.lift _ κ h0) t) = Sec.map κ t := by
    intro t; rw [← secMap_comp, kernel.lift_ι]
  refine ⟨fun a b hab => hi ?_, fun y => ?_⟩
  · rw [← hc, ← hc, hab]
  · obtain ⟨t, ht⟩ := hs (Sec.map (kernel.ι _) y) (by rw [← secMap_comp, kernel.condition, secMap_zero])
    exact ⟨t, kerSec_inj _ U (by rw [hc, ht])⟩

theorem LeafKumMu_of (h8 : A8) (h10 : A10) (hU : LeafKumMuUnits) : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumMu := by
  intro _ q _ B _ hq
  obtain ⟨κ, hκ⟩ := LeafKumMuSec_of hU q B hq
  have b1 := h8 ℤ (ZMod q) (Int.castRingHom (ZMod q)) (sp B) (tw q 1) 1
  have b2 := h10 ℤ (sp B) κ hκ 1
  exact ⟨((AddEquiv.ofBijective _ b1).trans (AddEquiv.ofBijective _ b2)).symm⟩

end LateralTheory.E.H2CurveOrder.LeafKumMuPf

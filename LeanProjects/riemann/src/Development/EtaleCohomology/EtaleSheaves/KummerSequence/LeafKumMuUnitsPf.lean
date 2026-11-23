import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf

def Gen (q : ℕ) (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
    Sec.map κ (U := U) (twGen 1 ζ) = (ofRings.sec unitsF U ⟨Additive.ofMul u⟩ : Sec Gm U)

def LeafKumMuMap : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, κ ≫ LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q = 0 ∧ Gen q κ

def LeafKumMuInj : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∀ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, Gen q κ →
    ∀ U : Scheme.{0}, Nonempty (Sx (sp B) 0 U) → Function.Injective (Sec.map κ (U := U))

def LeafKumMuSurj : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∀ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, Gen q κ →
    ∀ U : Scheme.{0}, Nonempty (Sx (sp B) 0 U) →
      ∀ s : Sec Gm U, Sec.map (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q) s = 0 → ∃ t, Sec.map κ t = s

theorem LeafKumMuUnits_of (hM : LeafKumMuMap) (hI : LeafKumMuInj) (hS : LeafKumMuSurj) :
    LateralTheory.E.H2CurveOrder.LeafKumMuPf.LeafKumMuUnits := by
  intro q _ B _ hq
  obtain ⟨κ, h0, hg⟩ := hM q B hq
  exact ⟨κ, h0, fun U hU => ⟨hI q B hq κ hg U hU, hS q B hq κ hg U hU⟩⟩

end LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf

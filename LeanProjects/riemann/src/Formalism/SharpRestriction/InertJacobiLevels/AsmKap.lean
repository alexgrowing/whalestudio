import Formalism.SharpRestriction.InertJacobiLevels.EtaSz
import Formalism.SharpRestriction.GrowthBounds.DefsInst

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.G

def gdOf (R : Ranks) : GC.GD := ⟨R, ⟨∅, ∅, 0, fun _ => PrimeClass.splitK⟩, fun _ => 0⟩

def glOf (R : Ranks) (sc : Scale) (Sc eta : ℝ) : GC.GParameters (gdOf R) := ⟨sc, Sc, eta⟩

def epOf (Ce : ℝ) (R : Ranks) (sc : Scale) : ℕ → ℕ :=
  fun p => ⌈Ce * (R.f : ℝ) * (R.k : ℝ) ^ 2 * Real.logb p sc.a⌉₊

def kapSetV (R : Ranks) (sc : Scale) (Sc : ℝ) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    Set ℝ :=
  {κ | 0 ≤ κ ∧
    ∀ (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
      [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
      (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
      UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
      ∀ lam0 : Fin n' → Fin (R.k - 1 + 1) → ℤ, IsBaseWeight TT a b ⌊4 * Sc⌋₊ lam0 → IsDominant lam0 →
        LPprime (W := W) p n' ι σ w 1 lam0 ⌈GC.tIf K (glOf R sc Sc 0) p n' TT a b⌉₊ (GC.DIf K (glOf R sc Sc 0) p n') κ
          (8 * (GC.DIf K (glOf R sc Sc 0) p n' + 1))}

def kapIOf (R : Ranks) (sc : Scale) (Sc : ℝ) (K : Consts) : KapI :=
  fun p n' TT a b => sInf (kapSetV R sc Sc K p n' TT a b)

theorem kapISet_eq {D : D7} (L : SizeData₂ D) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    kapISet L K p n' TT a b = kapSetV D.R L.sc L.Sc K p n' TT a b := rfl

theorem defs_of_shared {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : Consts) (Ce : ℝ) {R : Ranks} {sc : Scale}
    {Sc : ℝ} (hR : D.R = R) (hsc : L.sc = sc) (hSc : L.Sc = Sc) (hep : X.ep = epOf Ce R sc)
    (hk : X.kapI = kapIOf R sc Sc K) : EpDef X Ce ∧ KapIDef X K := by
  subst hR hsc hSc
  exact ⟨fun p => by rw [hep]; rfl, fun p n' TT a b => by rw [hk, kapISet_eq]; rfl⟩

theorem TieHyp.defs {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {C : FC} {R : Ranks} {sc : Scale} {Sc : ℝ}
    (H : TieHyp gatT L0 (kapIOf R sc Sc C.GK) (epOf C.cX.Ce R sc)) (hR : D.R = R) (hsc : L0.sc = sc)
    (hSc : L0.Sc = Sc) (Λ : LatIn D) : EpDef (H.Gx C.GK C.Cr Λ) C.cX.Ce ∧ KapIDef (H.Gx C.GK C.Cr Λ) C.GK :=
  defs_of_shared (H.Gx C.GK C.Cr Λ) C.GK C.cX.Ce hR hsc hSc rfl rfl

end Formalism.MainNotions.Inhab

end

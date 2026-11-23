import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.SecPsiMulPow
import Formalism.SharpRestriction.GrowthBounds.DataG

noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.G Formalism.FrobeniusOrbits

section Const

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

abbrev placesConst (hS : HidaSetting p n' W Qq O Kf ι σ j w) (nV m r : ℕ) (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ)
    (dom : ∀ v, IsDominant (lam0 v)) : Places p O Kf where
  w := w
  nV := nV
  n' := fun _ => n'
  W := fun _ => W
  Qq := fun _ => Qq
  ι := fun _ => ι
  σ := fun _ => σ
  j := fun _ => j
  setting := fun _ => hS
  m := m
  r := r
  lam0 := lam0
  dom := dom

end Const

section Host

variable {p : ℕ} {φ : Formalism.HC.Frame} (h : φ.MA) {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def placesHost (hS : HidaSetting p (orderOf (zPsi φ h)) W Qq O Kf ι σ j w) (m r : ℕ) (lam : φ.Psi → Fin (m + 1) → ℤ)
    (hlam : ∀ g, Antitone (lam g)) : Places p O Kf :=
  placesConst hS (nOrb (zPsi φ h)) m r (fun v s => lam (posG (zPsi φ h) ⟨v, s⟩)) (fun _ _ => hlam _)

variable (hS : HidaSetting p (orderOf (zPsi φ h)) W Qq O Kf ι σ j w) (m r : ℕ) (lam : φ.Psi → Fin (m + 1) → ℤ)
  (hlam : ∀ g, Antitone (lam g))

def posHost : (Σ v : Fin (placesHost h hS m r lam hlam).nV, Fin ((placesHost h hS m r lam hlam).n' v)) ≃ φ.Psi :=
  posG (zPsi φ h)

end Host

end Formalism.L2.G

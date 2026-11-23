import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain

namespace GlobalTheory.CoefDuty

variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb}

def Built (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) : Prop :=
  ∃ Sp : NdSpec A.pl M C big L.X L.T, Nonempty (AutSpec A M tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam)

def BuiltEx (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) : Prop :=
  ∀ big, ∃ L, Built A M C tup big L

def EvO (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (P : D7 → Prop) : Prop :=
  ∃ big, ∀ L, Built A M C tup big L → P (withLoc L)

def ExtOf (L₀ L₁ : LocAll (lay0 D)) (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc) : Prop :=
  L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ ∧
    Nonempty (LocExt L₀.lay.fixZ.nd L₁.lay.fixZ.nd L₀.lay.fixZ.naut L₁.lay.fixZ.naut i₀ i₁)

end GlobalTheory.CoefDuty

end

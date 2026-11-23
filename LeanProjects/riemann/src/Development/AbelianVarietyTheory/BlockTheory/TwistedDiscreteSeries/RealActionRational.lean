import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealActionRational

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def fockOf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (e : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) :
    WO (Vc D i) (Wc D i) → ℂ :=
  R.ptP i t (R.ioP i e w)

def levelForms (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Submodule ℂ (Bridge.Gf (Vc D i) → (R.cV i).W) :=
  Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ

def integrand (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : Bridge.Gf (Vc D i) → (R.cV i).W)
    (e : LowT (R.MW i (sg0 D A))) (g : GA D (Wc D i)) (h : GA D (Vc D i)) : ℂ :=
  thetaKO (R.ωP i t) h g (fockOf R i t e ((R.cV i).ext f h))

structure RealActionAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop where

  act : ∀ u ∈ GinfC (Vc D i), ∀ (e : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W),
    R.ωP i t (u, 1) (fockOf R i t e w) = fockOf R i t e ((R.cV i).ρ u w)

  ratFin : ∀ γ ∈ GQ (Vc D i), ∀ γf ∈ GfC (Vc D i), finHom (Vc D i) γf = finHom (Vc D i) γ →
    ∀ h ∈ GfC (Vc D i), ∀ (g : GA D (Wc D i)) (e : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W),
      thetaKO (R.ωP i t) (γf * h) g (fockOf R i t e ((R.cV i).ρ γ w)) = thetaKO (R.ωP i t) h g (fockOf R i t e w)

  left : ∀ f ∈ levelForms R i t, ∀ (e : LowT (R.MW i (sg0 D A))) (g : GA D (Wc D i)), ∀ γ ∈ GQ (Vc D i),
    ∀ h : GA D (Vc D i), integrand R i t f e g (γ * h) = integrand R i t f e g h

  right : ∀ f ∈ levelForms R i t, ∀ (e : LowT (R.MW i (sg0 D A))) (g : GA D (Wc D i)), ∀ u ∈ GinfC (Vc D i),
    ∀ h : GA D (Vc D i), integrand R i t f e g (h * u) = integrand R i t f e g h

def RealActionFock : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → ∀ (i : Fin D.R.m) (t : T), RealActionAt R i t

example (R : RealDat D A Ks) (F : Face D A) (hR : R.Char F) (i : Fin D.R.m) (t : T) :
    LinearMap.range (R.HV i t).e = levelForms R i t :=
  (hR.models.HV i t).2.1

example (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (x : (R.HV i t).H) (e : LowT (R.MW i (sg0 D A)))
    (g : GA D (Wc D i)) (h : GA D (Vc D i)) :
    integrand R i t ((R.HV i t).e x) e g h = thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i e (R.extV i t x h))) :=
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.RealActionRational

end

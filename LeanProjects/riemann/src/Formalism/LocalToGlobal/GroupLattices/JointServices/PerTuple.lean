import Formalism.LocalToGlobal.GroupLattices.JointServices.ValIntNonneg
import Formalism.LocalToGlobal.GroupLattices.JointServices.Cut

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.DIV Formalism.L2.Indef

noncomputable section

namespace Formalism.L2.G.ServJoint

def BaseT (D : D7) (μ : D.what₂.Tup) : Prop := μ = D.what₂.mu0 ∨ μ = D.what₂.muStar ∨ μ = D.what₂.muStar'

def TwT (D : D7) (μ : D.what₂.Tup) : Prop := (∃ w, μ = D.what₂.muAt w) ∧ ¬ BaseT D μ

def StabLL (D : D7) (μ : D.what₂.Tup) : Prop :=
  ∀ (a : 𝓞 D.what₂.LL), ∀ x ∈ (D.what₂.Mtilde μ).carrier, D.what₂.embLL (a : D.what₂.LL) • x ∈ (D.what₂.Mtilde μ).carrier

def AIntAt (D : D7) (μ : D.what₂.Tup) : Prop :=
  ∀ x, x ∈ (D.what₂.Mtilde μ).carrier → ((D.what₂.restRowsFiniteGroupCard : ℂ) • D.what₂.eOp μ x) ∈ (D.what₂.Mtilde μ).carrier

structure FormAt (D : D7) (μ : D.what₂.Tup) : Prop where
  ded : IsDedekindDomain D.what₂.O
  int : ∃ ι : D.what₂.O →+* 𝓞 D.what₂.LL, Function.Injective ι ∧ ∀ a, ((ι a : 𝓞 D.what₂.LL) : D.what₂.LL) = D.what₂.OtoLL a
  aint : AIntAt D μ
  form : OForm (D.what₂.Mtilde μ)

def Rd (D : D7) (μ : D.what₂.Tup) : Prop := StabLL D μ ∨ FormAt D μ

def StabUsed (D : D7) : Prop := ∀ μ, DV.Used D μ → StabLL D μ

structure OTieS (D : D7) : Prop where
  base : ∀ μ, BaseT D μ → FormAt D μ
  tw : ∀ μ, TwT D μ → StabLL D μ

def RdUsed (D : D7) : Prop := ∀ μ, DV.Used D μ → Rd D μ

def CutPl (D : D7) : Prop := ∀ w : D.what₂.places.Pl, CutUp D (D.what₂.muAt w)

end Formalism.L2.G.ServJoint

end

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT

namespace GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def LowIrr (M : DSModel V S) : Prop :=
  ∀ τ, IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (lowKSub (M.ε τ) (M.lam τ) (M.σ τ))

end Model

def ModelLow : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), LowSm M ∧ LowIrr M

section Base

variable {D : D7}

abbrev pW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D τ)).1

abbrev qW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D τ)).2

theorem pW_add_qW (i : Fin D.R.m) (τ : D.what₂.Tau) : pW i τ + qW i τ = (Wc D i).rank :=
  sig_sum _ (D.sp.W_sig _) _

def blockIx (i : Fin D.R.m) (τ : D.what₂.Tau) : Fin (pW i τ) ⊕ Fin (qW i τ) ≃ Fin (Wc D i).rank :=
  finSumFinEquiv.trans (finCongr (pW_add_qW i τ))

def blockWeight₂ (i : Fin D.R.m) (τ : D.what₂.Tau) : Fin (Wc D i).rank → ℝ := fun a =>
  ((Formalism.L2.NTheta.kapW (D.hc τ) (pW i τ) (qW i τ) ((blockIx i τ).symm a) : ℤ) : ℝ)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (A) in

structure BaseHol : Prop where
  lab_eq : ∀ ρ : D.what₂.Tau, lab (sg0 D A) ρ = ρ
  labE_eq : ∀ ρ : D.what₂.Tau, labE (sg0 D A) ρ = tauE D ρ
  par_eq : ∀ (i : Fin D.R.m) (ρ : D.what₂.Tau), parAt (Wc D i) (sg0 D A) ρ =
    Formalism.L2.NTheta.holPar (pW i ρ) (qW i ρ) (Formalism.L2.NTheta.kapW (D.hc ρ) (pW i ρ) (qW i ρ))

def WeightIs (R : RealDat D A Ks) : Prop :=
  ∀ (i : Fin D.R.m) (τ : D.what₂.Tau),
    Formalism.QuantumDeterminants.lowK ((R.MW i (sg0 D A)).ε τ) ((R.MW i (sg0 D A)).lam τ) = blockWeight₂ i τ

end Base

def BaseWeight : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    BaseHol A ∧ (R.models_order → WeightIs R)

def LowType : Prop := ModelLow ∧ BaseWeight

end GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType

end

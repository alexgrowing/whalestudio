import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalHeckeLifts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLocAt (V : HSp D) (PP : Pl D.host.E) (x : Bridge.Gf V) : Prop :=
  ∃ (f : AE D) (α : GA D V), Formalism.L2.JoinChr.IsPlIdem D f PP ∧ α ∈ GfC V ∧ Mult.SuppF V f α ∧ (x : GL _ _) = finHom V α

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev levV (R : RealDat D A Ks) (j : Fin D.R.m) (t : T) : Subgroup (Bridge.Gf (Vc D j)) :=
  (levEnv (Vc D j) (R.βV j) (R.datVt j t)).J

def IsInertOp (R : RealDat D A Ks) (j : Fin D.R.m) (t : T)
    (a : Pl D.host.E × Bridge.Gf (Vc D j) × Finset (Bridge.Gf (Vc D j))) : Prop :=
  Lev.IsConjPl a.1 a.1 ∧ a.1 ∉ R.Sb ∧ a.1 ∉ R.Q t ∧ IsLocAt (Vc D j) a.1 a.2.1 ∧
    (∀ y ∈ a.2.2, IsLocAt (Vc D j) a.1 y) ∧ Bridge.IsDC (levV R j t) a.2.1 a.2.2

abbrev InertOp (R : RealDat D A Ks) (j : Fin D.R.m) (t : T) : Type := {a // IsInertOp R j t a}

abbrev SphOp (R : RealDat D A Ks) (j : Fin D.R.m) (t : T) : Type := (A.ok t × ℕ) ⊕ InertOp R j t

abbrev OpW (R : RealDat D A Ks) : Type :=
  ∀ (j : Fin D.R.m) (t : T), SphOp R j t → Module.End ℂ (R.HW j (sg0 D A)).H

def Intertwines (R : RealDat D A Ks) (hW : OpW R) : Prop :=
  ∀ (j : Fin D.R.m) (t : T),
    (∀ (i : A.ok t × ℕ) (f : (A.MtCSD j t).Forms),
      R.thG j t (R.jV j t (A.heckeL j t i f)) = hW j t (Sum.inl i) (R.thG j t (R.jV j t f))) ∧
    ∀ a : InertOp R j t, ∃ TV : Module.End ℂ (R.HV j t).H,
      (∀ x, (R.HV j t).e (TV x) = Bridge.dcOp a.1.2.2 ((R.HV j t).e x)) ∧
        R.thG j t ∘ₗ TV = hW j t (Sum.inr a) ∘ₗ R.thG j t

def Commutes (R : RealDat D A Ks) (hW : OpW R) : Prop := ∀ j, Formalism.L2.Col.PairComm (hW j A.μ0)

def HasResC {K : Type} [Field K] [NumberField K] [StarRing K] (B : BlockDat K G Pl0) (σ : K →+* ℂ)
    (Sg : Pl0 → K[X]) (x : B.Pl × ℕ → ℂ) : Prop :=
  ∀ P, Formalism.L2.Col.heckePoly B.n B.q x P = (Sg (B.pl P) * B.blockProd P).map σ

def Parts (R : RealDat D A Ks) (hW : OpW R) : Prop :=
  ∀ (j : Fin D.R.m) (p : A.fam.base.Ix),
    R.Wp j p = Formalism.L2.Col.eigSum (hW j A.μ0) fun x =>
      HasResC (A.fam.L j A.μ0) D.what₂.embLL (trLift A.r D.R.m A.t A.q A.etaVal p.1) fun i => x (Sum.inl i)

def HeckeLiftsAt (R : RealDat D A Ks) : Prop :=
  ∃ hW : OpW R, Intertwines R hW ∧ Commutes R hW ∧ Parts R hW

def HeckeLifts : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → HeckeLiftsAt R

end GlobalTheory.IndefiniteRowSideFullHecke.LocalHeckeLifts

end

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalDataValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLocalAt (V : HSp D) (PP : Pl D.host.E) (x : Bridge.Gf V) : Prop :=
  ∃ (e : AE D) (g : GA D V), Formalism.L2.NTheta.IsIdemAt e PP ∧ g ∈ GfC V ∧ SuppAt e V g ∧ x = (finHom V).rangeRestrict g

def IsCosetSys (V : HSp D) (J : Subgroup (Bridge.Gf V)) (PP : Pl D.host.E) (k : ℕ) (S : Finset (Bridge.Gf V)) : Prop :=
  ∃ α : GA D V, IsHeckeAt V PP k α ∧ Bridge.IsDC J ((finHom V).rangeRestrict α) S ∧ ∀ a ∈ S, IsLocalAt V PP a

def IsUnifIdele (PP : Pl D.host.E) (x : (AE D)ˣ) : Prop :=
  ∃ (e : AE D) (ϖ : 𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e PP ∧ ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2 ∧
    (x : AE D) = Formalism.L2.JoinChr.locE D e (ϖ : D.host.E)

def coefB (μ η : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (x : (AE D)ˣ) : ℂ :=
  ((μ x : Circle) : ℂ) * (((η x : Circle) : ℂ))⁻¹ * ((Real.sqrt (Nat.card (kP PP) : ℝ) : ℝ) : ℂ)

def ScalarsIn (μ η : (AE D)ˣ →* Circle) (PP : Pl D.host.E) {K : Type} [Field K] (σ : K →+* ℂ) : Prop :=
  ∀ x : (AE D)ˣ, IsUnifIdele PP x → ((μ x : Circle) : ℂ) ∈ σ.range ∧ coefB μ η PP x ∈ σ.range

def embKs (D : D7) (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL] : Ks →+* ℂ :=
  D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)

def RationalCharacterValues (C : Formalism.L2.Host.CharFrame D) {K : Type} [Field K] (σ : K →+* ℂ) : Prop :=
  (∀ j, (C.mu0 j).ValuesIn 0 σ) ∧ C.eta.ValuesIn (1 / 2) σ

section Stmt

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T) : Subgroup (Bridge.Gf (Vc D i)) := (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J

def ratForm (i : Fin D.R.m) (t : T) (x : A.fam.amb.FL i t) : Bridge.Gf (Vc D i) → (R.cV i).W :=
  (R.HV i t).e (R.jV i t x)

def KeepsAt (i : Fin D.R.m) (t : T) (PP : Pl D.host.E) (k : ℕ) : Prop :=
  ∃ TV : Module.End D.what₂.LL (A.fam.amb.FL i t), ∀ S, IsCosetSys (Vc D i) (levV R i t) PP k S →
    ∀ x, ratForm R i t (TV x) = Bridge.dcOp S (ratForm R i t x)

def KeepsRational : Prop :=
  ∀ (i : Fin D.R.m) (t : T), ∀ P ∈ A.ok t, ∀ k ≤ (Vc D i).rank, KeepsAt R i t (R.pl P) k

def ScalarsLL : Prop :=
  ∀ (i : Fin D.R.m) (t : T), ∀ P ∈ A.ok t, ScalarsIn (R.mu0 ((i : ℕ) + 1)) R.eta (R.pl P) D.what₂.embLL

def ScalarsKs : Prop :=
  ∀ (i : Fin D.R.m) (t : T), ∀ P ∈ A.ok t, ScalarsIn (R.mu0 ((i : ℕ) + 1)) R.eta (R.pl P) (embKs D Ks)

def TransferRational : Prop :=
  KeepsRational R ∧ ScalarsLL R ∧ (RationalCharacterValues R.C (embKs D Ks) → ScalarsKs R)

def LocalDataExist : Prop :=
  ∀ (i : Fin D.R.m) (t : T), ∀ P ∈ A.ok t,
    (∀ k ≤ (Vc D i).rank, ∃ S, IsCosetSys (Vc D i) (levV R i t) (R.pl P) k S) ∧ ∃ x, IsUnifIdele (R.pl P) x

def ScalarsTupleLL : Prop :=
  ∀ (i : Fin D.R.m) (t : T), ∀ P ∈ A.ok t, ScalarsIn (R.toLevCh.mu t ((i : ℕ) + 1)) R.eta (R.pl P) D.what₂.embLL

variable {R}

end Stmt

def TransferRationalAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → TransferRational R

end GlobalTheory.IndefiniteRowSideFullHecke.LocalDataValues

end

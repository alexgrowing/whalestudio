import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.DataRRMetric

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev IsDedekindDomain NumberField Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

def dualSys (c : Sys D) : Sys D := fun P d => c P (dualLab d)

open Classical in

def badF (R : RealDat D A Ks) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  R.Pg.image fun PP => PP.under (𝓞 D.host.F)

def partE (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (c : Sys D) : Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) (badF R) c ⊓ R.EEat P

def partW (R : RealDat D A Ks) (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (c : Sys D) :
    Submodule ℂ (MMap (R.MW i (sg0 D A))) :=
  partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) (badF R) c ⊓
    R.Wat i (sg0 D A) P

def OccE (R : RealDat D A Ks) (c : Sys D) : Prop :=
  dualSys c ∈ IxFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badF R) R.e0

def OccW (R : RealDat D A Ks) (i : Fin D.R.m) (c : Sys D) : Prop :=
  c ∈ IxFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) (badF R)
    (R.eWf i (sg0 D A))

def Occ (R : RealDat D A Ks) (c : Sys D) : Prop := OccE R c ∨ ∃ i, OccW R i c

def polAt (R : RealDat D A Ks) (c : Sys D) (P : Pl0) : ℂ[X] :=
  Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (splitLab D.R.r k)

def IsLabel (R : RealDat D A Ks) (c : Sys D) (p : A.fam.base.Ix) : Prop :=
  ∀ P ∈ A.ok A.μ0, polAt R (dualSys c) P = RealDat.polE (A := A) p.1 P

def SplitDet (R : RealDat D A Ks) : Prop :=
  ∀ c c' : Sys D, Occ R c → Occ R c' →
    (∀ P : Pl0, Formalism.IndefR.Bridge.SplitOff (R.pl P) (R.Sb : Set (Pl D.host.E)) → polAt R c P = polAt R c' P) → c = c'

variable {X : DivX D}

def IndexTie (R : RealDat D A Ks) (E : EigIdx D X) (sys : E.Pi → Sys D) : Prop :=
  Function.Injective sys ∧ (∀ c, Occ R (sys c)) ∧ ∀ s, Occ R s → ∃ c, sys c = s

def RowTie (R : RealDat D A Ks) (F : Face D A) (E : EigIdx D X) (sys : E.Pi → Sys D) (jE : D.what₂.EE →ₗ[ℂ] R.HE.H) : Prop :=
  Function.Injective jE ∧ LinearMap.range jE = (R.EEat (R.levR F true)).comap R.HE.e ∧
    ∀ c, (DV.EEcpart D E c).map jE = (partE R (R.levR F true) (sys c)).comap R.HE.e

def LiftTie (R : RealDat D A Ks) (F : Face D A) (E : EigIdx D X) (sys : E.Pi → Sys D)
    (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H) : Prop :=
  ∀ i : Fin D.R.m, Function.Injective (jW i) ∧
    LinearMap.range (jW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e ∧
    ∀ c, (DV.sum₃ E ((i : ℕ) + 1) c).map (jW i) =
      (partW R i (R.levL F false (sg0 D A)) (sys c)).comap (R.HW i (sg0 D A)).e

def PartsOf (R : RealDat D A Ks) (E : EigIdx D X) (jE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H) (piOf : E.Pi → A.fam.base.Ix) : Prop :=
  Function.Injective piOf ∧
    (∀ c, (DV.EEcpart D E c).map jE ≤ R.EEp (piOf c)) ∧
    ∀ (i : Fin D.R.m) c, (DV.sum₃ E ((i : ℕ) + 1) c).map (jW i) ≤ R.Wp i (piOf c)

def PartsRow (R : RealDat D A Ks) (F : Face D A) (E : EigIdx D X) : Prop :=
  ∀ s : ℕ, A.fam.Ok s → R.Char F →
    SplitDet R ∧
    ∀ (sys : E.Pi → Sys D) (jE : D.what₂.EE →ₗ[ℂ] R.HE.H)
      (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H),
      IndexTie R E sys → RowTie R F E sys jE → LiftTie R F E sys jW →
        ∃ piOf : E.Pi → A.fam.base.Ix, (∀ c, IsLabel R (sys c) (piOf c)) ∧ PartsOf R E jE jW piOf

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]

example : dualLab (splitLab 3 1) = [1, 0, 0] := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem

end

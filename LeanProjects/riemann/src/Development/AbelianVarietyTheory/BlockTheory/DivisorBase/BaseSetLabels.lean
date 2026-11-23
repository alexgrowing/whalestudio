import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.DataRRMetric

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseSetLabels

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (D) in

abbrev Eig : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

variable (D) in

def IsBaseSet (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ v, v ∈ S ↔ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal

def dualEig (c : Eig D) : Eig D := fun P d => c P (dualLab d)

section Concrete

variable (R : RealDat D A Ks) (F : Face D A) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))

def EEc (P : LevelP R.Pg D.R.r ℂ) (c : Eig D) : Submodule ℂ R.HE.H :=
  (partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) S c ⊓ R.EEat P).comap R.HE.e

def Wc' (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (c : Eig D) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) S c ⊓
    R.Wat i (sg0 D A) P).comap (R.HW i (sg0 D A)).e

def OccW (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (c : Eig D) : Prop :=
  c ∈ IxFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) S (R.eWf i (sg0 D A))

def OccE (P : LevelP R.Pg D.R.r ℂ) (c : Eig D) : Prop :=
  dualEig c ∈ IxFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) S R.e0

abbrev conjugateBaseLevel : LevelP R.Pg D.R.r ℂ := R.levL F false (sg0 D A)

def hPol (c : Eig D) (P : Pl0) : ℂ[X] :=
  Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (splitLab D.R.r k)

def IsLabel (c : Eig D) (p : A.fam.base.Ix) : Prop :=
  ∀ P ∈ A.ok A.μ0, RealDat.polW (A := A) p.1 P = hPol R c P

def Occurs (c : Eig D) : Prop :=
  (∃ i, OccW R S i (conjugateBaseLevel R F) c) ∨ OccE R S R.triv c ∨ ∃ b, OccE R S (R.levR F b) c

def SplitDetermines : Prop :=
  ∀ c c', Occurs R F S c → Occurs R F S c' → (∀ P ∈ A.ok A.μ0, hPol R c P = hPol R c' P) → c = c'

end Concrete

section Ties

variable (R : RealDat D A Ks) (F : Face D A) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {X : DivX D} (E : EigIdx D X)
  (eig : E.Pi → Eig D) (jE : D.what₂.EE →ₗ[ℂ] R.HE.H)
  (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H)

def TieIdx : Prop :=
  Function.Injective eig ∧ ∀ c, c ∈ Set.range eig ↔ ∃ i, OccW R S i (conjugateBaseLevel R F) c

def TieRows : Prop :=
  Function.Injective jE ∧ LinearMap.range jE = (R.EEat (R.levR F true)).comap R.HE.e ∧
    ∀ π, (DV.EEcpart D E π).map jE = EEc R S (R.levR F true) (eig π)

def TieLifts : Prop :=
  ∀ i, Function.Injective (jW i) ∧
    LinearMap.range (jW i) = (R.Wat i (sg0 D A) (conjugateBaseLevel R F)).comap (R.HW i (sg0 D A)).e ∧
    ∀ π, (DV.sum₃ E ((i : ℕ) + 1) π).map (jW i) = Wc' R S i (conjugateBaseLevel R F) (eig π)

def Tied : Prop :=
  IsBaseSet D S ∧ TieIdx R F S E eig ∧ TieRows R F S E eig jE ∧ TieLifts R F S E eig jW

def HasLabel : Prop := ∀ π, ∃ p, IsLabel R (eig π) p

def LabelInj : Prop := ∀ π π' p, IsLabel R (eig π) p → IsLabel R (eig π') p → π = π'

def PartRows : Prop := ∀ π p, IsLabel R (eig π) p → (DV.EEcpart D E π).map jE ≤ R.EEp p

def PartLifts : Prop :=
  ∀ (i : Fin D.R.m) π p, IsLabel R (eig π) p → (DV.sum₃ E ((i : ℕ) + 1) π).map (jW i) ≤ R.Wp i p

def PartsAt : Prop :=
  HasLabel R E eig ∧ LabelInj R E eig ∧ PartRows R E eig jE ∧ PartLifts R E eig jW

end Ties

def PartsSt (D : D7) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (s : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (X : DivX D) (E : EigIdx D X) (eig : E.Pi → Eig D)
    (jE : D.what₂.EE →ₗ[ℂ] R.HE.H) (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H),
    A.fam.Ok s → R.Char F → Tied R F S E eig jE jW → PartsAt R E eig jE jW

section Basic₂

variable {R : RealDat D A Ks} {F : Face D A} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {X : DivX D} {E : EigIdx D X}
  {eig : E.Pi → Eig D} {jE : D.what₂.EE →ₗ[ℂ] R.HE.H}
  {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

example : dualLab (splitLab 3 1) = [1, 0, 0] := by decide

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.BaseSetLabels

end

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

section Abstract

variable {G K V : Type} [Group G] [Fintype G] [Field K] [AddCommGroup V] [Module ℂ V]

def typePart (ρ : Representation ℂ G V) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) : Submodule ℂ V where
  carrier := {x | ∀ g : P, ρ (g : G) x = σ ((ψ g : Kˣ) : K) • x}
  add_mem' := by
    intro x y hx hy g
    rw [map_add, hx g, hy g, smul_add]
  zero_mem' := by
    intro g
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro a x hx g
    rw [map_smul, hx g, smul_comm]

open Classical in

def typeIdem (ρ : Representation ℂ G V) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) : V →ₗ[ℂ] V :=
  (Nat.card P : ℂ)⁻¹ • ∑ g : P, (σ ((ψ g : Kˣ) : K))⁻¹ • ρ (g : G)

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowsOfLevel (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ (b : Bool) (x : R.HE.H),
    R.HE.e x ∈ R.EEat (R.levR F b) ↔
      ∀ g : (F.lvl b).P, R.gE (g : G) x = D.what₂.embLL (((F.lvl b).ψ g : D.what₂.LLˣ) : D.what₂.LL) • x

def RowsOfLevelIdem (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ b : Bool, (R.EEat (R.levR F b)).comap R.HE.e =
    LinearMap.range (typeIdem R.gE D.what₂.embLL (F.lvl b).P (F.lvl b).ψ)

def RowsOfLevelCx (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ b : Bool, (R.toCx F).EEl b = LinearMap.range (typeIdem (R.gEx F) A.v0.embedding (F.lvl b).P (F.lvl b).ψ)

def RowsOfLevelAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → RowsOfLevel R F

end GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

end

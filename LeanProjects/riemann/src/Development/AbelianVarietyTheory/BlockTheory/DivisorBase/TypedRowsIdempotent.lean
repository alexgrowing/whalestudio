import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.TypedRowsIdempotent

section TypeVec

variable {G K V : Type} [Group G] [Field K] [AddCommGroup V] [Module ℂ V]

def typePart (ρ : Representation ℂ G V) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) : Submodule ℂ V where
  carrier := {x | ∀ g : P, ρ (g : G) x = σ ((ψ g : Kˣ) : K) • x}
  add_mem' hx hy g := by rw [map_add, hx g, hy g, smul_add]
  zero_mem' g := by rw [map_zero, smul_zero]
  smul_mem' c x hx g := by rw [map_smul, hx g, smul_comm]

open Classical in

def typeIdem [Fintype G] (ρ : Representation ℂ G V) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) : V →ₗ[ℂ] V :=
  ((Nat.card P : ℂ))⁻¹ • ∑ g : P, σ (((ψ g)⁻¹ : Kˣ) : K) • ρ (g : G)

example (ρ : Representation ℂ G V) (σ : K →+* ℂ) : typePart ρ σ ⊥ 1 = ⊤ := by
  refine eq_top_iff.2 fun x _ g => ?_
  have : (g : G) = 1 := Subgroup.mem_bot.1 g.2
  simp [this]

end TypeVec

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowsOfLevel (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ (b : Bool) (x : R.HE.H), R.HE.e x ∈ R.EEat (R.levR F b) ↔
    ∀ g : (F.lvl b).P, R.gE (g : G) x = D.what₂.embLL (((F.lvl b).ψ g : D.what₂.LLˣ) : D.what₂.LL) • x

def RowsOfLevelIdem (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ b : Bool, (R.EEat (R.levR F b)).comap R.HE.e =
    LinearMap.range (typeIdem R.gE D.what₂.embLL (F.lvl b).P (F.lvl b).ψ)

def RowsOfLevelCx (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ (b : Bool) (x : (R.toCx F).EE), x ∈ (R.toCx F).EEl b ↔
    ∀ g : (F.lvl b).P, R.gEx F (g : G) x = A.v0.embedding (((F.lvl b).ψ g : D.what₂.LLˣ) : D.what₂.LL) • x

def RowsOfLevelOfChar (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → RowsOfLevel R F

end GlobalTheory.IndefiniteRowSideFullHecke.TypedRowsIdempotent

end

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev levV (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Subgroup (GA D (Vc D i)) :=
  levG (Vc D i) (R.βV i) (R.toLevCh.datVt i t)

abbrev chV (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (κ : GA D (Vc D i)) : ℂ :=
  levChi (Vc D i) (R.βV i) (R.toLevCh.datVt i t) κ

abbrev levW (R : RealDat D A Ks) (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) :=
  levG (Wc D i) (R.βW i) (R.toLevCh.datWp i R.toLevCh.triv)

def VecLevelAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  VecLaw (R.ωP i t) (levV R i t) (fun κ => (chV R i t κ)⁻¹) (levW R i) (fun _ => 1) (R.vP i t)

def VecLevelOf (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → R.thP_ωP → R.thP_vP → ∀ (i : Fin D.R.m) (t : T), VecLevelAt R i t

theorem principalLevelCharacter_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (R.toLevCh.datWp i R.toLevCh.triv) k = 1 := by
  have h : ∀ x, Formalism.L2.DIV.ext1 (R.toLevCh.datWp i R.toLevCh.triv).P.H (R.toLevCh.datWp i R.toLevCh.triv).P.chi x = 1 :=
    fun x => subgroupCharExtension_one_apply _ x
  unfold levChi Formalism.L2.DIV.levFn
  rw [h]
  simp [LevCh.datWp, datY]

end

def VecLevel (D : D7) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), VecLevelOf R

end GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters

end

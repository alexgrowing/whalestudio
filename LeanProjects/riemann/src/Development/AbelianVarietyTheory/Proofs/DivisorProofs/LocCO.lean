import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

def IsCO (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Prop :=
  IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
    IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))

def LocCO {n : ℕ} {w : Pl D.host.E} (K : Subgroup (GL (Fin n) (Kw w))) : Prop :=
  IsOpen (K : Set (GL (Fin n) (Kw w))) ∧ ∃ C : Set (GL (Fin n) (Kw w)), IsCompact C ∧ (K : Set (GL (Fin n) (Kw w))) ⊆ C

end GlobalTheory.FunObj

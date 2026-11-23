import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Enl0 (B B' : Base) : Prop :=
  B'.toPre = B.toPre ∧ B'.embLL '' (B'.Ks : Set B'.LL) = B.embLL '' (B.Ks : Set B.LL) ∧
    B.embLL '' (B.LL0 : Set B.LL) ⊆ B'.embLL '' (B'.LL0 : Set B'.LL) ∧ Set.range B.embLL ⊆ Set.range B'.embLL

theorem isBaseEnlargementFixedCoefField_of_coeffEnlargement {B B' : Base} (h : Enl B B') : Enl0 B B' := ⟨h.1, h.2.1, h.2.2.1.ge, h.2.2.2⟩

theorem enlarges_refl (B : Base) : Enl0 B B := ⟨rfl, rfl, subset_rfl, subset_rfl⟩

def DatExt0 : Prop := StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' ∧ Ext z z'

theorem datExt_of_datExt0 (h : DatExt0) : DatExt :=
  StepW.trans h (StepW.of_all fun _ _ _ _ _ _ _ H B f T w e => H B f T w (isBaseEnlargementFixedCoefField_of_coeffEnlargement e))

end GlobalTheory.Mem.R3.Rw

end

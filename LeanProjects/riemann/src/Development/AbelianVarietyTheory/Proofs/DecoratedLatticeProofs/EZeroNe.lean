import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.ColTest
open GlobalTheory.Fam

section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} {a : GeoAll W u}

def cst1 (a : GeoAll W u) : Cst a := ⟨fun _ _ => 1, fun _ => ⟨0, Fin.elim0, Fin.elim0⟩, fun _ _ => 1, fun _ _ => 0, fun _ => 1, fun _ _ => 1⟩

variable {k : Cst a} {row : ∀ t, RowCh (pk W) (lvP W) u a.g t} {col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))}
  {w₀ w : ∀ t, VTup ((a.fam row col).t t)} {F : ∀ t, GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)}

theorem places (h : ColOut k w₀ w F) (t) (p) : p ∈ (w t).Q ↔ ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 D.host.F) := by
  obtain ⟨pl, hp⟩ := (h.lev t).places
  rw [(h.same t).1, (h.pins t).places]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(pl i).1, (pl i).2, (hp i).2⟩
  · rintro ⟨PP, hP, rfl⟩
    refine ⟨pl.symm ⟨PP, hP⟩, ?_⟩
    rw [(hp _).2, Equiv.apply_symm_apply]

end Gen

section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

end True
end GlobalTheory.Fam.ColTest

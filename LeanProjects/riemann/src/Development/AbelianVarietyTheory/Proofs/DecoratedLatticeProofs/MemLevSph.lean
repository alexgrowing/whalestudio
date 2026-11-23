import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TopVol
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

def datSph (W : RealPack ex) : LevDat (I.rec7 l Z).host.E ℂ (I.rec7 l Z).sp.X'.rank :=
  { datXP (pk W) (lvP W) W.P.A3.A.μ0 with Q := ∅ }

def levSph (W : RealPack ex) (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :=
  (Formalism.IndefR.Lev.levG _ (pk W).βX (datSph W)).comap (MulAut.conj x⁻¹).toMonoidHom

def levTw (W : RealPack ex) (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (t : W.P.T) : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :=
  (Formalism.IndefR.Lev.levG _ (pk W).βX (datXP (pk W) (lvP W) t)).comap (MulAut.conj x⁻¹).toMonoidHom

theorem mem_levSph {W : RealPack ex} {x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'} (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :
    h ∈ levSph W x ↔ x⁻¹ * h * x ∈ levS _ (pk W).βX (datSph W) := by
  simp [levSph, levS, MulAut.conj_apply]

theorem mem_levTw {W : RealPack ex} {x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'} {t : W.P.T} (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :
    h ∈ levTw W x t ↔ x⁻¹ * h * x ∈ levS _ (pk W).βX (datXP (pk W) (lvP W) t) := by
  simp [levTw, levS, MulAut.conj_apply]

end GlobalTheory.TopVol

end

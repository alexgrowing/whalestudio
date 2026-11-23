import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.MiS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

def TwStd (W : RealPack ex) : Prop :=
  ∃ (l0 : I.Law0 l) (t : SymmetricTwistedColumnsAtPrimes W.R.T.n.tp W.R.T.cols (I.tw l l0 Z)),
    ex.tw = I.tw l l0 Z ∧ HEq W.R.T.tw t ∧ I.StdTw l Z l0 t

def FamCol {W : RealPack ex} {u : (I.rec7 l Z).what₂.Word} (f : FamCh W u) : Prop :=
  ∃ c₀, PinX I l Z (pk W).ψ (pk W).θ f.g.x f.g.vac c₀ ∧ ∀ t : W.P.T,
    (∃ (Ch₀ : ℕ → Type) (A : TwDat I l Z u (W.P.I.tup t) Ch₀) (ι : ∀ j, (f.col t).Ch j → Ch₀ j) (w : _),
      PinChL (pk W) f.g (f.col t) c₀ A ι w) ∧
    ∃ UT ε, PinTopL (pk W) f.g (lvP W) (t := t) (f.col t) UT ε

end GlobalTheory.AdForm

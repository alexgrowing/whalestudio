import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiStd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIntIn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.Fam.TopLoc.LocalIdempotentDensity
open GlobalTheory.SymBridge Formalism.L2.Col

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

def rowZero (hstd : Formalism.L2.Theta.IsStdChar (I.rec7 l Z) (pk W).ψ (-1)) (g : Geo (I.rec7 l Z)) (t : W.P.T) :
    RowCh (pk W) (lvP W) u g t where
  vP := fun _ => 0
  vT := fun _ _ => 0
  sBF := fun _ _ _ => Classical.choice (GlobalTheory.Unf.Inhab.nonempty_stepBF hstd _ _)
  sFB := fun _ _ _ => Classical.choice (GlobalTheory.Unf.Inhab.nonempty_stepFB hstd _ _)
  io := fun _ => 0
  ioT := fun _ _ => 0

theorem idem_at (hW : AllTrue W) (a : GeoAll W u) (ha : a.Is) (n : Fin a.n) :
    Formalism.L2.NTheta.IsIdemAt (a.G n).q.e (a.pl n).1 :=
  ((ha.tie (fun t => rowZero W.Q.stdChar a.g t) (fun t => colNone t)).2.idem n).1

end GlobalTheory.Fam.TopLoc.LocalIdempotentDensity

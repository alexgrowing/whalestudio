import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts HidaSetting WInputsLink h0)
namespace GlobalTheory.ExpTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
section Point
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
def NumStAlt : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j, ∃ (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W ∧ NumOk P W
open Classical in
def ExponentSumStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
  ∀ t w, LIncl (blk p j t) (lvlL p) (subZ p j t) w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w))
def ModelStatement : Prop := _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i p => ∀ j (P : Par) (W : Wts (Fm.D x i).what₂.Tau), Dict (Fm.L x i) j P W → NumOk P W →
  ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ModelAt p j P W w
end GlobalTheory.ExpTie
end
end

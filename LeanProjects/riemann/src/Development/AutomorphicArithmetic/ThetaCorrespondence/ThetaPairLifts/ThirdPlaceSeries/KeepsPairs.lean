import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace
variable {D : D7} {c : Comm D} {v : VCom c}
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
def KeepsPairsAlt (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (κ : GA D (D.sp.X 0)) : Prop :=
  ∀ i (g : GL (Fin (D.sp.X 0).rank) a.k), (mt (D.sp.X 0) κ).map (a.o.p i).pr = (a.o.β 0 i).b * g.val * (a.o.β 0 i).b' →
    g • a.o.Q 0 i = a.o.Q 0 i
def TraceAtElement (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (κ : GA D (D.sp.X 0)) : Prop :=
  ∀ i g, IsMatrixInFrameOfXZero (a.G i) κ g → GlobalTheory.RootEx.embX ((a.G i).s + 1) g ∈ (((a.G i).S.T (Fin D.R.t)).lev 0 ((a.G i).s + 1) (Nat.zero_add _)).J
def InLevelGroup (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (κ : GA D (D.sp.X 0)) : Prop :=
  GlobalTheory.FinPl.Moves (D.sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => True) ∧ _root_.GlobalTheory.FamTrace.KeepsPairsAlt a κ ∧ _root_.GlobalTheory.FamTrace.TraceAtElement a κ
def LevelAtElement (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (x : GA D (Yc D 0)) : Prop :=
  ∀ i m, (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m → m ∈ (((a.G i).S.T (Fin D.R.t)).lev 0 ((a.G i).s + 1) (Nat.zero_add _)).J
def InLevelGroupOfY (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (x : GA D (Yc D 0)) : Prop :=
  GlobalTheory.FinPl.Moves (Yc D 0) x (a.v.N 0) (a.v.N 0) (fun p => p ∉ a.v.gP) ∧ _root_.GlobalTheory.FamTrace.LevelAtElement a x
end GlobalTheory.FamTrace
end
end

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
namespace GlobalTheory.QPl
variable {D : D7} {c : Comm D} {v : VCom c} {t : Tup c}
end GlobalTheory.QPl
namespace GlobalTheory.Fam
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
def QuadraticExtensionData.eps {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (α : J.Ch j) : GA (I.rec7 l Z) (Yc (I.rec7 l Z) j) →₀ ℂ :=
  if (∃ ρ, j + 2 * ρ + 2 = (I.rec7 l Z).R.m) ∨ j = 0 then J.wt j α • conv (List.ofFn fun i => (J.E i).εL j (α i)) else 0
variable (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t)
def columnChoiceOfCoefficients (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)))
    (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ)
    (S : ∀ t j, GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j)
    (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ) (t : W.P.T) :
    ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t)) where
  kom := kom t
  Ch := (J t).Ch
  dd := dd t
  e := fun j α => (s t j α • (J t).eps j α).mapDomain (· * a.g.b j)
  eT := fun n _ β => (s t n β • Finsupp.single (1 : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') ((J t).wt n β)).mapDomain (· * a.g.bT)
  Ram := fun j => {φ | (J t).A.RamL (J t).ι j φ}
  S := S t
  rd := fun j α φ y => if hj : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j hj ((J t).ι j α) φ y else 0
  cV := cV t
  cK := cK t
  cP := cP t
def trivialColumnChoice (t : W.P.T) : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t)) where
  kom := fun _ => 1
  Ch := fun _ => Empty
  dd := fun _ α => α.elim
  e := fun _ α => α.elim
  eT := fun _ _ α => α.elim
  Ram := fun _ => ∅
  S := fun _ φ => φ
  rd := fun _ α => α.elim
  cV := 0
  cK := 0
  cP := 0
def familyOfRowColumnChoices (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t)))
    (hCh : ∀ t, (col t).Ch = (J t).Ch) (t : W.P.T) : GlobalTheory.QPl.QFam a.v ((a.fam row col).t t) where
  χ := _root_.GlobalTheory.Fam.chrK_alt W t
  r := (J t).r
  Q := fun i => ((J t).E i).toAt
  eqv := fun j => Equiv.cast (congrFun (hCh t) j)
end GlobalTheory.Fam
end
end

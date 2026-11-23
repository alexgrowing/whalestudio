import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamCol
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GVec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamAllQ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero

set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (a : _root_.GlobalTheory.Fam.GeometricFamily W u)
structure FamilyConstants where
  ε : ℕ → a.ι → 𝓀[a.k]ˣ
  op : ∀ j, BiOp (D.sp.X j) (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1))
  r : ℕ → a.ι → ℝ
  e : ℕ → a.ι → ℤ
  cG : ℕ → ℂ
  sc : W.P.T → ℕ → ℂ
variable {a} (k : _root_.GlobalTheory.Fam.FamilyConstants a)
abbrev FamilyConstants.v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g) := (a.v.withT (a.o.S k.ε) k.op).withCG k.cG
variable {row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t} {col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))}
structure ColumnOutputCondition (w₀ w : ∀ t, VTup ((a.fam row col).t t))
    (F : ∀ t, GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)) : Prop where
  ok : (a.fam row col).ColOK
  pins : ∀ t, (F t).Pins (w₀ t)
  same : ∀ t, (w t).Q = (w₀ t).Q ∧ (w t).eQ = (w₀ t).eQ ∧ (w t).eQT = (w₀ t).eQT ∧ (w t).cQ = (w₀ t).cQ ∧ (w t).FY = (w₀ t).FY ∧
    (w t).FT = (w₀ t).FT
  laws : ∀ t, QLaw a.v (w t) ∧ QLast a.v (w t) ∧ QFin a.v (w t)
  lev : ∀ t, _root_.GlobalTheory.Fam.QLevAlt (a.fam row col) (F t)
  vec : ∀ t, _root_.GlobalTheory.Fam.RationalVectorCondition (a.fam row col) (w₀ t)
  FY : ∀ t j f, f ∈ (w₀ t).FY j ↔ ∀ i, ((F t).Q i).Typed j f
  FT : ∀ t f, f ∈ (w₀ t).FT
  FX : ∀ t j, j + 2 ≤ D.R.m → ∀ ψ ∈ (col t).Ram j, ∀ α y, (col t).rd j α ψ y ∈ (w t).FX j α
  atQ : ∀ t j, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w₀ t).eQ j) ∧ (∀ h, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w₀ t).eQT j h)) ∧
    ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ (w₀ t).Q) ((w t).dQ j α γ)
  e : ∀ t j α, (col t).e j α = ((w t).ε j α).mapDomain (· * a.g.b j) ∧
    ∀ g ∈ ((w t).ε j α).support, g ∈ GlobalTheory.FinPl.grpAt (Yc D j) (· ∈ (w₀ t).Q)
  eT : ∀ t n h β, (col t).eT n h β = ((w t).εT n h β).mapDomain (· * a.g.bT) ∧
    ∀ g ∈ ((w t).εT n h β).support, g ∈ GlobalTheory.FinPl.grpAt D.sp.X' (· ∈ (w₀ t).Q)
  dd : ∀ t j, j < D.R.m → ∀ α γ f, IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ f → comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((col t).dd j α γ) f =
    comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((w t).dQ j α γ) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) f))
  read : ∀ t, ∃ S₀, ReadS a.o ((a.fam row col).t t) k.ε S₀
  sc : ∀ t, (w t).sc = k.sc t
  cT : ∀ t j ρ h, (w t).cT j = a.o.mono (k.r j) (k.e j) ((row t).sBF j ρ h).χW
  cv : ∀ t, CVEq k.v (w t)
  cK : ∀ t j, j < D.R.m → UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W t) ((col t).cK j) ((col W.P.A3.A.μ0).cK j)
  cP : ∀ t, UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W t) (col t).cP (col W.P.A3.A.μ0).cP
  zero : _root_.GlobalTheory.MiTop.ChartAtZeroCondition (a.fam row col)
end Gen
section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
def LevelCondition' (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg ∧ (∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ↔ PP ∈ (B.primes X).vGs) ∧ ∀ t, (_root_.GlobalTheory.Fam.pk_z W).xiH t = I.xi (W.P.I.tup t)
structure AllFamilyConditions (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop where
  pk : _root_.GlobalTheory.Fam.PackageHypotheses W
  tr : _root_.GlobalTheory.Fam.ValidRealPackage W
  tq : _root_.GlobalTheory.Fam.GeometricFamilyConditions W
  tw : _root_.GlobalTheory.AdForm.TwStdAlt W
  lev : _root_.GlobalTheory.Fam.LevelCondition' W
  rc : Nonempty (_root_.Formalism.IndefR.IndefiniteRealisationRecursion W.Q)
end True
end GlobalTheory.Fam
end
end

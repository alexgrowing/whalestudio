import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt

set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {D : D7}
section Package
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (u : D.what₂.Word) (g : Geo D)
variable {R P u g}
end Package
section Read
variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)
end Read
section Real
open GlobalTheory.MiS
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
abbrev pk_z := W.Q.Rl.toRealDat
abbrev complexLevelStructure : LevelP (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ℂ := (_root_.GlobalTheory.Fam.pk_z W).levR W.Q.F.lv2 true
def LevelCondition (u : D.what₂.Word) (μ : D.what₂.Tup) (x : GA D D.sp.X') (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (μ = D.what₂.mu0 → LevG (W.R.T.cols.forms u).clsP.toG x J χ) ∧ ∀ h : μ ≠ D.what₂.mu0, LevG (W.R.T.tw.pt.cls u μ h) x J χ
def ReadsCoefficients (u : D.what₂.Word) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (μ : D.what₂.Tup) (G : D.what₂.Amb μ)
    (f : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) : Prop :=
  (∀ h : μ = D.what₂.mu0, ReadsG (W.R.T.cols.forms u).clsP.toG (W.R.T.cols.forms u).valP.eW j x
    ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) G h)) f) ∧
  ∀ h : μ ≠ D.what₂.mu0, ReadsG (W.R.T.tw.pt.cls u μ h) (W.R.T.tw.pt.val u μ h).eW j x ((D.eMtTw u μ).symm G) f
def leadingLinearMap (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA D D.sp.X' → ℂ) :=
  (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)))
def LeadingReadAt (u : D.what₂.Word) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') : Prop :=
  GlobalTheory.Core.Rk.Top.IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j ∧ x ∈ GfC D.sp.X' ∧ ∀ t : W.P.T,
    _root_.GlobalTheory.Fam.LevelCondition W u (W.P.I.tup t) x (levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) ∧
    ∀ (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL) (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL),
      HEq F F' → _root_.GlobalTheory.Fam.ReadsCoefficients W u j x (W.P.I.tup t) (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F)) (_root_.GlobalTheory.Fam.leadingLinearMap W t F')
def LeadingReadStatement : Prop := ∃ x, ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt W u j x
def tailCoefficient (u : D.what₂.Word) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (μ : D.what₂.Tup)
    (ψ : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ) (f : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) : ℂ :=
  if h : ∃ G, _root_.GlobalTheory.Fam.ReadsCoefficients W u j x μ G f then
    if h0 : μ = D.what₂.mu0 then
      (D.mem u).P.Ptil (Eq.rec (motive := fun C _ => C.cls D.R.m → C.Y D.R.m → ℂ)
        (Eq.rec (motive := fun ν _ => (D.chTw u ν).cls D.R.m → (D.chTw u ν).Y D.R.m → ℂ) ψ h0) (D.memberColumns_twistedChain_base u))
        ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) h.choose h0))
    else (D.PTw u μ).Ptil ψ ((D.eMtTw u μ).symm h.choose)
  else 0
structure FamilyCharacter (u : D.what₂.Word) where
  g : Geo D
  j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)
  row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u g t
  col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))
variable {W} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
abbrev FamilyCharacter.c : Comm D := commOf (_root_.GlobalTheory.Fam.pk_z W) u f.g
abbrev FamilyCharacter.t (t : W.P.T) : Tup f.c :=
  tupOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u f.g t (f.row t) (f.col t) fun ψ F => _root_.GlobalTheory.Fam.tailCoefficient W u f.j f.g.bT (W.P.I.tup t) ψ F.1
end Real
end GlobalTheory.Fam
end
end

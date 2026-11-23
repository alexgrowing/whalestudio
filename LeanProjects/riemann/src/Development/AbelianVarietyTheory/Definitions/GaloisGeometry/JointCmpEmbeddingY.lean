import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TiedCls
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.InertKernelTheory.ProjRSurj
import Formalism.LocalToGlobal.InertKernelTheory.TieSerPin
import Formalism.LocalToGlobal.HermitianColumns.FullSym
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot

noncomputable section

namespace GlobalTheory.TwV

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.SecondKernelSeries
open Formalism.L2.KerInert.AdmLoc (pendG CurveIn XiIn)
open GlobalTheory.TwU (StepCharts ChainCharts AdData AdPins AdTie AdLawAt AdDatum latCo ratA ssRec)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def castSt {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : StepCharts C i hi) : StepCharts C' i hi := h ▸ S

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure Joint (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv}
    (H : CmpJHyp ex.cmp I) (X : LabIn I) where
  Gd : GroupCompatibilityAll D hT ex.cmp
  St : ChainCharts D u μ
  A : AdData t u μ St
  dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt
  a : 𝓞 D.host.E
  pins : AdPins A dtU
  tie : AdTie A dtU a
  st : ∀ j (hj : j + 1 ≤ D.R.m), St (j + 1) hj = castSt (X.onCh j hj) (StepCharts.ofStepIn (I.at' j hj).st)
  e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0
  jointCmpEmbeddingY : (D.mem u).C.Y 0 ≃ (D.chTw u μ).Y 0
  e0Tw : ∀ φ c y, D.e0Tw u μ φ (e0 c) (jointCmpEmbeddingY y) = φ c y
  one : OneHyp ((Gd.forms u).cls0).toChart.lev (lev0At Gd u w hg).A ((Gd.forms u).cls0).toChart.y
  cls0 : ∀ c (La : (D.gat u w hg).P.Tup), (D.gat u w hg).P.IsLatTup La → X.c0.cls c La = e0 (levelZeroClass one c La)
  lev0 : ∀ β : (St 0 (Nat.zero_le _)).Ch, ((St 0 _).K β).lev.Lb = (Gd.forms u).cls0.lev.Lb ∧
    ((St 0 _).K β).lev.Uloc = (Gd.forms u).cls0.lev.Uloc ∧ ((St 0 _).K β).lev.U = (Gd.forms u).cls0.lev.U ∧
    ∀ (κ : ((St 0 _).K β).lev.U) (κ' : (Gd.forms u).cls0.lev.U), κ.1 = κ'.1 → ((St 0 _).K β).lev.chi κ = (Gd.forms u).cls0.lev.chi κ'
  ch0 : Subsingleton (St 0 (Nat.zero_le _)).Ch
  y0 : ∀ c, ∃ κ : (Gd.forms u).cls0.lev.U, ((St 0 (Nat.zero_le _)).y (e0 c)).1 = ((Gd.forms u).cls0.y c).1 * κ.1 ∧ (Gd.forms u).cls0.lev.chi κ = 1 ∧
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ q ∈ Dx.Qp μ, ((q : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) → bc (prV (E := D.host.E) v) κ.1 = 1
  fr0 : ∀ y, (St 0 (Nat.zero_le _)).eY (jointCmpEmbeddingY y) = (Gd.forms u).val0.eY y
  iw : ∀ j hj β v, ((I.at' j hj).st.loc β).iw v = (lev0At Gd u w hg).A.iw v
  oneB : ∀ j hj β β', ((I.at' j hj).st.loc β).B = ((I.at' j hj).st.loc β').B
  pos : ∀ j hj, (I.at' j hj).st.pos = hT.gat_pos u w hg
  tw : ∀ j hj β (x : UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm),
    Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 → ((I.at' j hj).st.tw β).ch x = D.chiD (dtU y) ^ cTw D (j + 1)
  rel : ∀ (N : ℕ) (M M' : SDLat D.host.E N), ∀ g ∈ Formalism.L2.Herm.UstdAf D.sp.cm N, Formalism.L2.Herm.Carries g M.1 M'.1 →
    ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y g → D.relDet N M M' = QuotientGroup.mk (dtU y)
  base : ∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)
  sharp : ∀ j < D.R.m, FormsSharpAt t u μ j
  dgen : IsDgen D t.cD
  tied : LatTied hT Gi Gl
  away : D.what₂.places.resChar w ∉ Dx.Qp μ
  cop : Nat.Coprime (Ideal.absNorm t.cc) (D.what₂.places.resChar w)
  empty : ∀ j, D.R.m < j → IsEmpty (Lv.comp j)
  alg : ∀ j hj β, SplAlg ((I.at' j hj).st.loc β)
  alg0 : SplAlg (lev0At Gd u w hg).A
  lbB : ∀ j hj β, LbAtB ((I.at' j hj).st.loc β) ((I.at' j hj).st.K β).lev.Lb
  lb0 : LbAtB (lev0At Gd u w hg).A (lev0At Gd u w hg).Lb
  pl : ∀ j hj β v, ((I.at' j hj).st.loc β).pl v = (lev0At Gd u w hg).A.pl v
  kin : ∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y

section Sys

variable {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} (H : CmpJHyp ex.cmp I) (X : LabIn I)
  [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg)

abbrev sysS : Sys (D.what₂.places.resChar w) :=
  sysAt (chainAt H hT) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg))
    (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT))
    (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le)

instance : IsFractionRing (sysS H X std).G.O (sysS H X std).G.Kf := Lt.fracAt Gl u w hg

variable {H X} {t : KerEntTied ex} (J : Joint t H X)

abbrev Joint.cp : ChartPts (sysS H X std) D :=
  cpAt (chainAt H hT) std _ _ _ _ _ (Lt.dGT_spec (kaAt X H hT)) _ I (lev0At J.Gd u w hg).A (lev0At J.Gd u w hg).J (lev0At J.Gd u w hg).Lb
    (lev0At J.Gd u w hg).Uloc

abbrev Joint.fd : FData (sysS H X std) D :=
  fdAtL (chainAt H hT) std _ _ _ _ _ (Lt.dGT_spec (kaAt X H hT)) _ I (lev0At J.Gd u w hg) J.a ∅

abbrev Joint.rho : ∀ v : (sysS H X std).Pl, D.host.E →+* (sysS H X std).G.P.Qq v := fun v => (lev0At J.Gd u w hg).A.iw v

def Joint.chart (j : ℕ) (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) : (J.St j hj).Ch := (J.St j hj).chOf (clsAt X H j La.1 La.2)

def Joint.IsPt (j : ℕ) (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j)
    (x : UPts (sigD D) (gramN D j hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  ∃ hr : ((sysS H X std).Pj j).m + 1 = D.R.N j, x.1 = Formalism.L2.PairingIndexBounds.F.reGL (finCongr hr) ((J.cp std).y j La)

def Joint.pt (j : ℕ) (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) : UPts (sigD D) (gramN D j hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  Classical.epsilon (J.IsPt std j hj La)

open Classical in

def Joint.xi0 (Xi : AdDatum J.St) (j : ℕ) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1))
    (z : Formalism.L2.Col.HomE D.host.E (((sysS H X std).Pj j).m + 1) (((sysS H X std).Pj (j + 1)).m + 1)) : ℂ :=
  if h : j + 1 ≤ D.R.m ∧ ((sysS H X std).Pj j).m + 1 = D.R.N j ∧ ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) then
    Xi j h.1 (J.chart std j _ La) (J.chart std (j + 1) h.1 La') (J.pt std j _ La) (J.pt std (j + 1) h.1 La')
      (homRe h.2.1 h.2.2 (Formalism.L2.Col.inFr ((J.fd std).trG j La).symm ((J.fd std).trG (j + 1) La').symm z))
  else 0

def Joint.Dict : Prop :=
  ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 →
    J.IsPt std j hj La (J.pt std j hj La) ∧
    (∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D j hj), ∃ κ : ((J.St j hj).K (J.chart std j hj La)).lev.U,
      (J.pt std j hj La).1 = ratA D.host.F γ * ((J.St j hj).y (clsAt X H j La.1 La.2)).1 * κ.1) ∧
    HEq ((J.fd std).kerN j La) (latK D.sp (gramN D j hj) J.a (J.pt std j hj La).1 ((J.St j hj).K (J.chart std j hj La)).lev.Lb) ∧
    (J.fd std).dt j La = Matrix.GeneralLinearGroup.det (J.pt std j hj La).1

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Joint.At where
  E : CEmbC (sysS H X std).G
  lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]
  hK : ∀ (z : D.what₂.LL) (hz : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ), E.iK (ex.cmp.embW u w hg z) = lam ⟨D.what₂.embLL z, hz⟩
  g : GL3Theta.G1 (D.what₂.places.resChar w)
  hLT : LTIso g
  curve : CurveIn D (D.what₂.places.resChar w) t.cc t.δ g t.B t.χ lam
  hfin : ∀ j c, ((sysS H X std).Lv.lev j c).FinClasses
  hst : FinStab (sysS H X std).Lv
  Xi : AdDatum J.St
  muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ
  law : AdLawAt J.A J.dtU J.a Xi muT

variable {std J} (S : J.At std)

abbrev Joint.At.Y : Pend (sysS H X std) :=
  pendG (sysS H X std) S.E S.hfin S.hst S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT

def Joint.At.Pair : Prop := GlobalTheory.TwU.PairOK (sysS H X std) (J.fd std) t.B t.χ (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (J.rho std)

def Joint.At.Move : Prop := GlobalTheory.TwU.MoveTie (sysS H X std) S.E.toCEmb (J.fd std) t.χ S.lam (J.xi0 std S.Xi) S.muT (J.rho std)

def Joint.At.Away : Prop := ∀ v, ∀ j < D.R.m,
  GlobalTheory.TwU.AwayTie (sysS H X std) S.E.toCEmb (J.fd std) t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (J.rho std) v j

def Joint.At.Pos : Prop := GlobalTheory.TwU.LamPos (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) S.lam (J.rho std)

def Joint.At.Scal : Prop := Lt.ScalGLt (sysS H X std) S.hfin (J.fd std) t.χ S.muT S.lam

def Joint.At.K1 : Prop :=
  Lt.ThetaSeriesDataHypothesesBelowMaximalLevel (sysS H X std) S.E S.hfin (hT.gat_pos u w hg) (J.fd std) t.χ S.lam (t.rd u μ).lev (J.xi0 std S.Xi) S.muT

def Joint.At.Law : Prop :=
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  GlobalTheory.TwU.KapLawLt (sysS H X std) ℂ_[D.what₂.places.resChar w] (thFOf (sysS H X std) (hT.gat_pos u w hg)
    (FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (ltC S.g S.hLT)))

def Joint.At.Del (j : ℕ) : Prop :=
  ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) →
    ∃ cK : ℂ_[D.what₂.places.resChar w], ‖cK‖ = 1 ∧
      KernelDifferenceAtLevel (Y := S.Y) t u μ (kaAt X H hT).cls (kaAt X H hT).cmp ι (rdJ I X.onCh ι) (srOf S.Y) j cK

end Sys

def AllSites (Q : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv}
    {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] {std : Lt.StdAtW D Gl u w hg} {t : KerEntTied ex}
    {J : Joint t H X}, J.At std → Prop) : Prop :=
  ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv}
    {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] {std : Lt.StdAtW D Gl u w hg} {t : KerEntTied ex}
    {J : Joint t H X} (S : J.At std), Q S

def JointsAt (t : KerEntTied ex) (μ : D.what₂.Tup) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ →
    ∃ (Lv : Levels (Gl.Fl u w hg)) (I : CmpJIn ex.tw u μ w hg Lv) (H : CmpJHyp ex.cmp I) (X : LabIn I), Nonempty (Joint t H X)

end GlobalTheory.TwV

end

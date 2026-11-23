import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 1000000
structure HeightCountingBaseData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) : Type 1 where
  host : HostTied D
  jE : D.host.E →+* Qb
  frame : ∀ x, jE x = host.fr.j x
  A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE
  cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT
  au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au
  row : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR
  fr : OmFrame D
  fr_jE : fr.jE = jE
  pht : PhtOn A.wd fr fun _ _ _ _ => True
  depth : RowDepth D rep
  elem : Elem D
  val : ValLL0 D cf
  labc : LabConj D A.wdT
  zeta : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen
  omax : Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x
section Rows
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
  {F : Face3 D A3} {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {cf : CharFrame D}
variable {Y cG}
structure SettingsFormsData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 where
  Bs : SideB D cf a.A.row (lowAll D) Pq n.S n.In.hL n.In.eig n.In.θ
  Sb_le : ∀ i, n.In.Sb ⊆ D.ntw.S0 i
  rootsOfUnityRing_le_wittIntegers : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D))
  lam : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z
variable (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1)
structure SeriesData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends toSettingsFormsState : _root_.GlobalTheory.HeightCounting.SettingsFormsData a n Pq where
  YS : NExpRealS R cG n.S
  eF : YS.eF = Bs.eF
  fi : ∀ i x, HEq ((YS.fi i).e x) x
  ser : SerAt YS g.v₀ Bs.exp PV cf Pq
  tau : TauTrue Bs.exp
structure ModuliPointsData (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends toSeriesState : _root_.GlobalTheory.HeightCounting.SeriesData g a n PV Pq where
  geo : Nonempty (GlobalTheory.GeoTie.ThetaTie YS g.fw D.nth)
variable {g}
structure HeightCountingCharacterData {a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf (repOf Y)} {n : InRat Y cG} {xi : D.what₂.Tup → HChar D.host.E}
    {Q : D.what₂.places.Pl → Finset (PlE D.host)} (m : InMt Y cf xi Q)
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} (b : _root_.GlobalTheory.HeightCounting.ModuliPointsData g a n m.ad.PV Pq)
    (k : D.what₂.places.Pl → ℕ) (psi : D.what₂.places.Pl → HChar D.host.E) : Type 1 where
  ch : NChoice D
  tp : TupTied D cf ch
  xi_eq : tp.xi = xi
  psi_eq : tp.psi = psi
  Q_eq : ch.Q = Q
  k_eq : ∀ w, TwistedAt D w → ch.k' w = k w
  side : ChoiceSide D cf m.M b.Bs.exp ch tp
  ok : ∀ w, TwistedAt D w → IntegralHeckeForms.TwOK (ch.twI w) (ch.k' w) (ch.Q w) ((ch.psi' w).comp (D.ntw.art (ch.twI w) (ch.Q w)))
  th : EMtTheta Y b.YS ch
structure RealExpansionExtraData {nch : NChoice D} {tp : TupTied D cf nch} {a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp} (r : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData a R F cG Y)
    (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (xd : ThData D) : Type 1 where
  ad : MtAd Y a.all.gal.mt
  fi : ∀ i x, HEq ((r.nexp.fi i).e x) x
  hecke : NExpHeckeRowX R cG _ r.nexp r.hecke fun _ => LinearMap.id
  cHk : ∀ i b P, ∃ u : (D.ntw.O i)ˣ, r.hecke.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u
  eig : ∃ Sb e, (∀ i, Sb ⊆ D.ntw.S0 i) ∧ HEq a.nt.eig e ∧ EigAd Y Sb e
  ser : SerAt r.nexp g.v₀ a.all.exp ad.PV cf a.Pq
  tau : TauTrue a.all.exp
  geo : Nonempty (GlobalTheory.GeoTie.ThetaTie r.nexp g.fw D.nth)
  ok : ∀ w, TwistedAt D w → IntegralHeckeForms.TwOK (nch.twI w) (nch.k' w) (nch.Q w) ((nch.psi' w).comp (D.ntw.art (nch.twI w) (nch.Q w)))
  th : EMtTheta Y r.nexp nch
  xd : XdAll xd
  large : GlobalTheory.CoefDuty.Large D
  labc : LabConj a.nt.D a.nt.A.wdT
  zeta : ∀ k, haveI : Fact (a.nt.D.host.g k).Prime := ⟨a.nt.D.host.g_prime k⟩
    a.nt.A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k)).gen
  pht : ∃ fr : OmFrame a.nt.D, fr.jE = a.nt.jE ∧ PhtOn a.nt.A.wd fr fun _ _ _ _ => True
end Rows
open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl in
def defaultExtension (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun _ _ _ _ w Z _ _ t _ _ xd c =>
  _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd
end GlobalTheory.HeightCounting
end
end

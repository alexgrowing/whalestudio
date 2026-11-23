import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitenessOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTiedRowLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MtAdLStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesAtOfExpRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkRowLStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigHkDatBackStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EmtThetaLStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GrpTieOfLCStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieOfTrue
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x)
theorem mtInput_of_levelC : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
  show MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * l.c.tp.xi μ) l.c.ch.Q
  rw [l.c.xi_eq, l.c.Q_eq]; exact l.mt.mt
variable {big : (Dof x).what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 (Dof x))} (Sp : NdSpec l.a.A.pl l.mt.M l.c.ch big L.X L.T)
  (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation l.a.A l.mt.M l.c.tp.tup Sp.iq L.Y L.C) (ss : ∀ σ lam, IsSSRep (L.Z.rbar σ lam))
def nTrueAtWeight : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
  { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row
    low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs
    M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := _root_.GlobalTheory.HeightCounting.Fin3.mtInput_of_levelC l, big := big, L := L, Sp := Sp, Au := Au, ss := ss
    eq := rfl, pack := rfl }
variable (L) in
structure AllLevelsData : Type 1 where
  a : _root_.GlobalTheory.HeightCounting.NAllCAlt (withLoc L) (chL L l.c.ch)
  chr : (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc L), TupTied (withLoc L) c (chL L l.c.ch)) = ⟨cfL L (cfOf x), tpL L l.c.tp⟩
  jE : a.gal.fr.jE = l.a.jE
  mt : a.gal.mt = mtL L l.mt.M
  exp : ExpRel L l.b.Bs.exp a.exp
  chrN : NCharTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  chrGal : NGalChrTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  loc : ∀ F : Formalism.L2.RowFrame (withLoc L), F.rep = repOf x.r.Y → _root_.Formalism.L2.RowLocTiedAlt (withLoc L) a.gal.lp F
variable (al : _root_.GlobalTheory.HeightCounting.Fin3.AllLevelsData l L) (hLg : GlobalTheory.CoefDuty.Large (withLoc L))
theorem pq_weight_eq (i j b k Q ψ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (hadm : Formalism.L2.NX.AdmTw (withLoc L) i k Q ψ) :
    plsOf al.a.exp i j b k Q ψ h1 h2 hadm = (qpOf (Dof x) l.Pq Q, qpOf (Dof x) l.Pq ((Dof x).ntw.pD i)) :=
  (al.exp.pl i j b k Q ψ h1 h2 hadm).trans (Prod.ext (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).1 (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).2)
def weightedAtData : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) where
  nt := _root_.GlobalTheory.HeightCounting.Fin3.nTrueAtWeight l Sp Au ss
  all := al.a
  chr_eq := al.chr
  host := ⟨(by with_unfolding_all exact (l.a.host.fr :)), (by with_unfolding_all exact (l.a.host.jLL :)), (by with_unfolding_all exact (l.a.host.embLL :))⟩
  frameN := fun y => (by with_unfolding_all exact (((congrArg (fun e : (Dof x).host.E →+* Qb => e ((y))) ((al.jE) : ((al.a.gal.fr.jE) : (Dof x).host.E →+* Qb) = l.a.jE)).trans (l.a.frame ((y)))) : _))
  chrN := al.chrN
  chrGal := al.chrGal
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  pq := fun i j b k Q ψ h1 h2 hadm => ⟨(by with_unfolding_all exact ((congrArg Prod.fst (_root_.GlobalTheory.HeightCounting.Fin3.pq_weight_eq l al i j b k Q ψ h1 h2 hadm)) :)),
    (by with_unfolding_all exact ((congrArg Prod.snd (_root_.GlobalTheory.HeightCounting.Fin3.pq_weight_eq l al i j b k Q ψ h1 h2 hadm)) :))⟩
  jE_eq := (by with_unfolding_all exact ((heq_of_eq al.jE.symm) :))
  mt_eq := (by with_unfolding_all exact ((heq_of_eq al.mt.symm) :))
  Pq_eq := (by with_unfolding_all exact ((HEq.refl l.Pq) :))
  low := (by with_unfolding_all exact ((low_ok (Dof x)) :))
  split := hLg.2.1
  ratIn := l.rat.In
  ratIn_hL := rfl
  ratIn_eig := rfl
  ratIn_θ := rfl
  depth := l.a.depth
def localAtData : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (DL x L) (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) (_root_.GlobalTheory.HeightCounting.Fin3.localCharacterTupleAgreement L l) := (by with_unfolding_all exact ((_root_.GlobalTheory.HeightCounting.Fin3.weightedAtData l Sp Au ss al hLg) :))
include l in
variable (L) in
theorem grpTie_famR : Formalism.L2.DIV.GrpTie (DL x L) (famR (w.st (oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) (datL x L).Xg (datL x L).tr).A
    (datL x L).F.P0 (datL x L).F.ψ0 (datL x L).F.P1 (datL x L).F.ψ1 ((datL x L).R.eG.trans (datL x L).cG) :=
  ⟨(by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).card :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).e0 :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).lvl0 :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).psi0 :)), (by with_unfolding_all exact ((_root_.GlobalTheory.T.grpTie_of_levelC l).idxSharp :)),
    (datL x L).pins.keep.psi.lvl⟩
variable {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y)
def normalizedRowDatum : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := DL x L) (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg) (datL x L).R (datL x L).F (datL x L).cG Y where
  kKs := kKsL L l.rat
  hk := hkL L l.rat
  nexp := _root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l
  hecke := _root_.GlobalTheory.HeightCounting.Fin3.localHeckeHeightData L l
  grp := _root_.GlobalTheory.HeightCounting.Fin3.grpTie_famR l L
  rowLoc := (by with_unfolding_all exact ((al.loc ((by with_unfolding_all exact ((frameY Y) :))) ((by with_unfolding_all exact ((eq_of_heq (kc% hY.rep : HEq (repOf Y) (kc% (repOf x.r.Y) : type_of% (repOf Y)))) :)))) :))
  S_eq := (by with_unfolding_all exact ((SL_heq L l.rat) :))
  hL_eq := (by with_unfolding_all exact ((HEq.refl l.rat.In.hL) :))
  rep_eq := (by with_unfolding_all exact (hY.rep.symm :))
theorem nonempty_nMore_of_xdAll {xd : ThData (Dof x)} (hxd : XdAll xd) : Nonempty (_root_.GlobalTheory.HeightCounting.RealExpansionExtraData (_root_.GlobalTheory.HeightCounting.Fin3.normalizedRowDatum l Sp Au ss al hLg Y hY) (datL x L).geo (xdD L xd)) := by
  obtain ⟨ad, had⟩ := _root_.GlobalTheory.T.exists_mtAd_psiVectorLocal_of_yRel L l Y hY
  obtain ⟨ser⟩ := _root_.GlobalTheory.T.series_at_local_of_exp_relation L l al.a.exp al.exp
  have e : (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).all.gal.mt = _root_.GlobalTheory.HeightCounting.Fin3.localMultiplicityFamily L l := (by with_unfolding_all exact (al.mt :))
  have H : ∃ ad' : MtAd Y (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).all.gal.mt, ad'.PV = _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l := by
    rw [e]; exact ⟨ad, had⟩
  obtain ⟨ad', had'⟩ := H
  have ser' : SerAt (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (expD L al.a.exp) ad'.PV (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.placeMapLocal L l) := had'.symm ▸ ser
  exact ⟨{ ad := ad'
           fi := _root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal_fi_e_heq L l
           hecke := _root_.GlobalTheory.T.hecke_expansion_local_of_levelC L l
           cHk := (by with_unfolding_all exact ((fun i b Q => (⟨l.b.Bs.cHk i b Q, pow_one _⟩ : ∃ u : ((Dof x).ntw.O i)ˣ, (_root_.GlobalTheory.HeightCounting.Fin3.heckeHeightData l).cHk i b 1 Q =
             algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)) u)) :))
           eig := ⟨_root_.GlobalTheory.HeightCounting.Fin3.smallPlaceSet L l, _root_.GlobalTheory.HeightCounting.Fin3.localEigenvalueDegree L l, (by with_unfolding_all exact (l.b.Sb_le :)), (by with_unfolding_all exact ((HEq.refl l.rat.In.eig) :)), _root_.GlobalTheory.T.eigAd_of_yRel_at_level_c L l Y hY⟩
           ser := (by with_unfolding_all exact (ser' :))
           tau := (by with_unfolding_all exact ((al.exp.tau l.b.tau) :))
           geo := _root_.GlobalTheory.HeightCounting.Fin3.thetaTie_yStructureLocal_nonempty L l
           ok := _root_.GlobalTheory.HeightCounting.Fin3.twist_ok_local L l
           th := _root_.GlobalTheory.T.emtTheta_of_yRel L l Y hY
           xd := xdD_all L hxd
           large := (by with_unfolding_all exact (hLg :))
           labc := (by with_unfolding_all exact (l.a.labc :))
           zeta := (by with_unfolding_all exact (l.a.zeta :))
           pht := (by with_unfolding_all exact ((⟨l.a.fr, l.a.fr_jE, l.a.pht⟩ : ∃ fr : Formalism.L2.OmFrame (Dof x), fr.jE = l.a.jE ∧ PhtOn l.a.A.wd fr fun _ _ _ _ => True) :)) }⟩
def localCharacterChoiceTwist : NchT w (oL x L).Z P.Wt (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) where
  tp := _root_.GlobalTheory.HeightCounting.Fin3.localCharacterTupleAgreement L l
  xi := (by with_unfolding_all exact (l.c.xi_eq :))
  psi := (by with_unfolding_all exact (l.c.psi_eq :))
  tie := (_root_.GlobalTheory.HeightCounting.NchAt.tie_of_true_alt (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).nt).1
  Q := fun v hv => ⟨(by with_unfolding_all exact (((congrFun l.c.Q_eq v).trans (GlobalTheory.HeightCounting.Up.Model.qOf_on v hv)) :)),
    (by with_unfolding_all exact ((l.c.k_eq v ((GlobalTheory.HeightCounting.Up.Model.twisted_iff x v).2 hv)) :))⟩
  chrPsi := (_root_.GlobalTheory.HeightCounting.NchAt.tie_of_true_alt (_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg).nt).2
include hY in
theorem exists_core_and_listPin {xd : ThData (Dof x)} (hxd : XdAll xd) (t : RowsT K w (oL x L).Z P.Wt p0) (hz : HEq t.r.z (datL x L))
    (ht : HEq t.r.Y Y) : ∃ c : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceCore hL t (_root_.GlobalTheory.HeightCounting.Fin3.localCharacterChoiceTwist l Sp Au ss al hLg),
      Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w (oL x L).Z P.Wt p0 t (_root_.GlobalTheory.HeightCounting.Fin3.characterChoiceLocal L l) (_root_.GlobalTheory.HeightCounting.Fin3.localCharacterChoiceTwist l Sp Au ss al hLg) (xdD L xd) c) ∧
      ∀ cDep : ℝ, ListSt cDep x → ListPin (DL x L) t.r.z.R.toRealDat.toLevCh cDep K.s.b := by
  obtain ⟨hX, ⟨z, intersectionNumber_baseChange, Y', Zr, tix⟩, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := t
  have e : z = datL x L := eq_of_heq hz
  subst e
  have e' : Y' = Y := eq_of_heq ht
  subst e'
  obtain ⟨mo⟩ := _root_.GlobalTheory.HeightCounting.Fin3.nonempty_nMore_of_xdAll l Sp Au ss al hLg Y' hY hxd
  exact ⟨⟨_root_.GlobalTheory.HeightCounting.Fin3.localAtData l Sp Au ss al hLg, _root_.GlobalTheory.HeightCounting.Fin3.normalizedRowDatum l Sp Au ss al hLg Y' hY, (by with_unfolding_all exact (l.sel :))⟩, ⟨(mo, ⟨bkL L⟩)⟩, fun cDep h => GlobalTheory.T.toricCharacterGridList_kept_localizedStage x L cDep h⟩
omit l in
theorem exists_read_heq_of_eq {Z : w.Lt} {z z' : Dat (w.st Z) w.I P.hX T P.Wt} (e : z = z') {p : BaseLevelRowSide (w.D Z)}
    (Y₀ : Read z.R.toRealDat z.F.lv2 p) : ∃ Y₁ : Read z'.R.toRealDat z'.F.lv2 p, HEq Y₁ Y₀ := by
  subst e
  exact ⟨Y₀, HEq.rfl⟩
omit l in
theorem start_at_all_pre2 : StepW Start fun K _ _ _ w => ∀ P : Pre2 K w, RowsAt P :=
  Step.trans GlobalTheory.Mem.R3.Rw.St.exists_rowsT (Step.of_all fun _ _ _ _ _ _ _ H w hs P => H w ⟨hs.1, ⟨P⟩⟩ P)
end GlobalTheory.HeightCounting.Fin3
end
end

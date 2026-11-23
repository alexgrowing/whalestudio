import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThirdLevelOfGoodTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NchTOfTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalHeckeDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NAllCWithLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingOfRowLiftFamilyMovedDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwDatPsiValuesInLL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataStateLocalisationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedReadingsRelatedLocalizedAdelicDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtOfExpRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricCharacterGridListKeptLocalizedStageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GroupTieOfLocalCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRowOfLocalAllStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMotiveAdjointWithLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdjointOfReadRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MotiveThetaOfReadRelationStatement

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (l : LC hL x)

theorem mtIn : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
  show MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * l.c.tp.xi μ) l.c.ch.Q
  rw [l.c.xi_eq, l.c.Q_eq]; exact l.mt.mt

theorem builtEx (hP : PrN) : GlobalTheory.CoefDuty.BuiltEx l.a.A l.mt.M l.c.ch l.c.tp.tup := fun big =>
  GlobalTheory.T.side_rational_hecke_data hP.what₂.art (Dof x) (cfOf x) l.a.jE l.a.A (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ l.b.Bs l.mt.M
    l.c.ch l.c.tp l.c.side (mtIn l) l.a.elem.star l.a.elem.int l.a.elem.split (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _)
    (fun v _ => by rw [l.c.psi_eq]; exact GlobalTheory.twDat_psi_valuesIn_LL B T P.coh v) l.a.omax
    (GlobalTheory.HeightCounting.blocksUnique_of_cgTrue hL hP.what₂.fin hP.what₂.gal hP.what₂.art hP.what₂.js hP.what₂.cheb _ _ l.a.cg) big

variable {big : (Dof x).what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 (Dof x))} (Sp : NdSpec l.a.A.pl l.mt.M l.c.ch big L.X L.T)
  (Au : AutSpec l.a.A l.mt.M l.c.tp.tup Sp.iq L.Y L.C) (ss : ∀ σ lam, IsSSRep (L.Z.rbar σ lam))

def ntW : NTrue hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
  { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row
    low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs
    M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := mtIn l, big := big, L := L, Sp := Sp, Au := Au, ss := ss
    eq := rfl, pack := rfl }

variable (L) in

structure AllL : Type 1 where
  a : NAllC (withLoc L) (chL L l.c.ch)
  chr : (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc L), TupTied (withLoc L) c (chL L l.c.ch)) = ⟨cfL L (cfOf x), tpL L l.c.tp⟩
  jE : a.gal.fr.jE = l.a.jE
  mt : a.gal.mt = mtL L l.mt.M
  exp : ExpRel L l.b.Bs.exp a.exp
  chrN : NCharTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  chrGal : NGalChrTied (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp)
  loc : ∀ F : Formalism.L2.RowFrame (withLoc L), F.rep = repOf x.r.Y → Formalism.L2.RowLocTied (withLoc L) a.gal.lp F

include Au ss in

theorem allL_nonempty (hP : PrN) (hA : ArchCmp hL) : Nonempty (AllL l L) := by
  obtain ⟨a, h1, h2, h3, h4, ⟨h5⟩, h6, h7⟩ := GlobalTheory.HeightCounting.FitAll.nAllC_withLoc hL hA.lp hA.cg _ (ntW l Sp Au ss).toNBuilt l.a.fr l.a.fr_jE
    l.a.pht l.a.elem (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _) Finset.subset_union_left
  exact ⟨⟨a, h1, h2, h3, h4, h5, h6, h7⟩⟩

theorem low_ok (D : D7) : 2 ∈ lowAll D ∧ AbsolutelyIrreducibleSpan.q0 D ∈ lowAll D ∧ (NumberField.discr D.host.E).natAbs.primeFactors ⊆ lowAll D ∧
    (Ideal.absNorm D.host.ccK).primeFactors ⊆ lowAll D := by
  refine ⟨by simp [lowAll, Formalism.L2.lowPr], by simp [lowAll, Formalism.L2.lowPr], fun p hp => ?_, fun p hp => ?_⟩ <;>
    simp only [lowAll, Formalism.L2.lowPr, Finset.mem_union, Finset.mem_insert] <;> tauto

variable (al : AllL l L) (hLg : GlobalTheory.CoefDuty.Large (withLoc L))

theorem pqW (i j b k Q ψ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (hadm : Formalism.L2.NX.AdmTw (withLoc L) i k Q ψ) :
    plsOf al.a.exp i j b k Q ψ h1 h2 hadm = (qpOf (Dof x) l.Pq Q, qpOf (Dof x) l.Pq ((Dof x).ntw.pD i)) :=
  (al.exp.pl i j b k Q ψ h1 h2 hadm).trans (Prod.ext (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).1 (l.b.Bs.pq i j b k Q ψ h1 h2 hadm).2)

def natW : NAt hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) where
  nt := ntW l Sp Au ss
  all := al.a
  chr_eq := al.chr
  host := ⟨(by with_unfolding_all exact (l.a.host.fr :)), (by with_unfolding_all exact (l.a.host.jLL :)), (by with_unfolding_all exact (l.a.host.embLL :))⟩
  frameN := fun y => (by with_unfolding_all exact (((congrArg (fun e : (Dof x).host.E →+* Qb => e ((by with_unfolding_all exact (y :)))) ((by with_unfolding_all exact (al.jE :)) : (kc% al.a.gal.fr.jE : (Dof x).host.E →+* Qb) = l.a.jE)).trans (l.a.frame ((by with_unfolding_all exact (y :))))) :))
  chrN := al.chrN
  chrGal := al.chrGal
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  pq := fun i j b k Q ψ h1 h2 hadm => ⟨(by with_unfolding_all exact ((congrArg Prod.fst (pqW l al i j b k Q ψ h1 h2 hadm)) :)),
    (by with_unfolding_all exact ((congrArg Prod.snd (pqW l al i j b k Q ψ h1 h2 hadm)) :))⟩
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

def natD : NAt hL (DL x L) (cfD x L) (chD L l) (tpD L l) := (by with_unfolding_all exact ((natW l Sp Au ss al hLg) :))

include l in
variable (L) in

theorem grpD : Formalism.L2.DIV.GrpTie (DL x L) (famR (w.st (oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) (datL x L).Xg (datL x L).tr).A
    (datL x L).F.P0 (datL x L).F.ψ0 (datL x L).F.P1 (datL x L).F.ψ1 ((datL x L).R.eG.trans (datL x L).cG) :=
  ⟨(by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).card :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).e0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).lvl0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).psi0 :)), (by with_unfolding_all exact ((GlobalTheory.T.group_tie_of_local_coefficient l).idxSharp :)),
    (datL x L).pins.keep.psi.lvl⟩

variable {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y)

def frameY : Formalism.L2.RowFrame (DL x L) := Formalism.L2.Col.rowFrameOf (DL x L) _ Y.eFT

def rowD : NRow (D := DL x L) (natD l Sp Au ss al hLg) (datL x L).R (datL x L).F (datL x L).cG Y where
  kKs := kKsL L l.rat
  hk := hkL L l.rat
  nexp := ysL L l
  hecke := hkHL L l
  grp := grpD l L
  rowLoc := (by with_unfolding_all exact ((al.loc ((by with_unfolding_all exact ((frameY Y) :))) ((by with_unfolding_all exact ((eq_of_heq (kc% hY.rep : HEq (repOf Y) (kc% (repOf x.r.Y) : type_of% (repOf Y)))) :)))) :))
  S_eq := (by with_unfolding_all exact ((SL_heq L l.rat) :))
  hL_eq := (by with_unfolding_all exact ((HEq.refl l.rat.In.hL) :))
  rep_eq := (by with_unfolding_all exact (hY.rep.symm :))

theorem moreD {xd : ThData (Dof x)} (hxd : XdAll xd) : Nonempty (NMore (rowD l Sp Au ss al hLg Y hY) (datL x L).geo (xdD L xd)) := by
  obtain ⟨ad, had⟩ := GlobalTheory.T.exists_motive_adjoint_with_levels L l Y hY
  obtain ⟨ser⟩ := GlobalTheory.T.series_at_of_exp_relation L l al.a.exp al.exp
  have e : (natD l Sp Au ss al hLg).all.gal.mt = mtD L l := (by with_unfolding_all exact (al.mt :))
  have H : ∃ ad' : MtAd Y (natD l Sp Au ss al hLg).all.gal.mt, ad'.PV = pvL L l := by
    rw [e]; exact ⟨ad, had⟩
  obtain ⟨ad', had'⟩ := H
  have ser' : SerAt (ysL L l) (datL x L).geo.v₀ (expD L al.a.exp) ad'.PV (cfD x L) (pqD L l) := had'.symm ▸ ser
  exact ⟨{ ad := ad'
           fi := ysL_fi L l
           hecke := GlobalTheory.T.hecke_row_of_local_all L l
           cHk := (by with_unfolding_all exact ((fun i b Q => (⟨l.b.Bs.cHk i b Q, pow_one _⟩ : ∃ u : ((Dof x).ntw.O i)ˣ, (hkH l).cHk i b 1 Q =
             algebraMap ((Dof x).ntw.O i) (FractionRing ((Dof x).ntw.O i)) u)) :))
           eig := ⟨sbD L l, eigD L l, (by with_unfolding_all exact (l.b.Sb_le :)), (by with_unfolding_all exact ((HEq.refl l.rat.In.eig) :)), GlobalTheory.T.eigen_adjoint_of_read_relation L l Y hY⟩
           ser := (by with_unfolding_all exact (ser' :))
           tau := (by with_unfolding_all exact ((al.exp.tau l.b.tau) :))
           geo := geoL L l
           ok := okL L l
           th := GlobalTheory.T.motive_theta_of_read_relation L l Y hY
           xd := xdD_all L hxd
           large := (by with_unfolding_all exact (hLg :))
           labc := (by with_unfolding_all exact (l.a.labc :))
           zeta := (by with_unfolding_all exact (l.a.zeta :))
           pht := (by with_unfolding_all exact ((⟨l.a.fr, l.a.fr_jE, l.a.pht⟩ : ∃ fr : Formalism.L2.OmFrame (Dof x), fr.jE = l.a.jE ∧ PhtOn l.a.A.wd fr fun _ _ _ _ => True) :)) }⟩

def nchD : NchT w (oL x L).Z P.Wt (chD L l) where
  tp := tpD L l
  xi := (by with_unfolding_all exact (l.c.xi_eq :))
  psi := (by with_unfolding_all exact (l.c.psi_eq :))
  tie := (GlobalTheory.HeightCounting.NchAt.tie_of_true (natD l Sp Au ss al hLg).nt).1
  Q := fun v hv => ⟨(by with_unfolding_all exact (((congrFun l.c.Q_eq v).trans (GlobalTheory.HeightCounting.Up.Model.qOf_on v hv)) :)),
    (by with_unfolding_all exact ((l.c.k_eq v ((GlobalTheory.HeightCounting.Up.Model.twisted_iff x v).2 hv)) :))⟩
  chrPsi := (GlobalTheory.HeightCounting.NchAt.tie_of_true (natD l Sp Au ss al hLg).nt).2

include hY in

theorem core_at {xd : ThData (Dof x)} (hxd : XdAll xd) (t : RowsT K w (oL x L).Z P.Wt p0) (hz : HEq t.r.z (datL x L))
    (ht : HEq t.r.Y Y) : ∃ c : NCore hL t (nchD l Sp Au ss al hLg),
      Nonempty (NEb hL K B f T w (oL x L).Z P.Wt p0 t (chD L l) (nchD l Sp Au ss al hLg) (xdD L xd) c) ∧
      ∀ cDep : ℝ, ListSt cDep x → ListPin (DL x L) t.r.z.R.toRealDat.toLevCh cDep K.s.b := by
  obtain ⟨hX, ⟨z, intersectionNumber_baseChange, Y', Zr, tix⟩, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := t
  have e : z = datL x L := eq_of_heq hz
  subst e
  have e' : Y' = Y := eq_of_heq ht
  subst e'
  obtain ⟨mo⟩ := moreD l Sp Au ss al hLg Y' hY hxd
  exact ⟨⟨natD l Sp Au ss al hLg, rowD l Sp Au ss al hLg Y' hY, (by with_unfolding_all exact (l.sel :))⟩, ⟨(mo, ⟨bkL L⟩)⟩, fun cDep h => GlobalTheory.T.toricCharacterGridList_kept_localizedStage x L cDep h⟩

omit l in
theorem read_cast {Z : w.Lt} {z z' : Dat (w.st Z) w.I P.hX T P.Wt} (e : z = z') {p : BaseLevelRowSide (w.D Z)}
    (Y₀ : Read z.R.toRealDat z.F.lv2 p) : ∃ Y₁ : Read z'.R.toRealDat z'.F.lv2 p, HEq Y₁ Y₀ := by
  subst e
  exact ⟨Y₀, HEq.rfl⟩

def RowsAt (P : Pre2 K w) : Prop := ∀ x : St P, (∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) →
  ∃ t : RowsT K w x.o.Z P.Wt x.s.p0, Nonempty (RXs t) ∧ t.hX = P.hX ∧ HEq t.r.z x.m.z ∧ HEq t.r.Y x.r.Y ∧ HEq t.r.Z.jW x.r.Z.jW

omit l in
variable (x L) in

theorem rows_ex (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (hD : GlobalTheory.Published.DiscreteSeriesExists) (hP : PrN) (hR : RowsAt P)
    (he : ∀ j v, 1 ≤ j → j ≤ B.R.m → etaL x L j v = P.q.eta j v) :
    ∃ (p : BaseLevelRowSide (w.D (oL x L).Z)) (t : RowsT K w (oL x L).Z P.Wt p), Nonempty (RXs t) ∧
      ∃ Y₁ : YT x L p, YRel L Y₁ ∧ HEq t.r.z (datL x L) ∧ HEq t.r.Y Y₁ := by
  obtain ⟨m, hm, hc, hco⟩ := GlobalTheory.T.exists_movedData_state_localisations x L
  obtain ⟨s, r, hpin⟩ := GlobalTheory.T.exists_reading_of_rowLiftFamily_movedData B f T w P.Z₀ P.hX P.Wt P.z P.q (oL x L)
    (GlobalTheory.LinksInputs.inputs_of_hypotheses hW hD hP.hc hP.decay (w.D (oL x L).Z)) (fitsL L) m
  obtain ⟨t, rx, -, hz, hy, -⟩ := hR ⟨oL x L, fitsL L, x.G_eq, x.etaF, bkL L, m, hc, hco, s, r, hpin⟩ he
  obtain ⟨Y₁, h1⟩ := read_cast hm r.Y
  exact ⟨s.p0, t, rx, Y₁, GlobalTheory.T.normalisedReadings_related_localizedAdelicData x L m hm hco s r hpin Y₁ h1, hz.trans (heq_of_eq hm), hy.trans h1.symm⟩

theorem lv3_of_third (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (hD : GlobalTheory.Published.DiscreteSeriesExists) (hP : PrN) (hA : ArchCmp hL)
    (hR : RowsAt P)
    (hE : GlobalTheory.CoefDuty.BuiltEx l.a.A l.mt.M l.c.ch l.c.tp.tup → GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
      GlobalTheory.CoefDuty.Large D' ∧ ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v)
    (hX : ∃ xd : ThData (Dof x), XdAll xd) (S : SExt) (Γ : GeoP) (N : NExt hL)
    (hN : ∀ Z p t nch n xd c, NEb hL K B f T w Z P.Wt p t nch n xd c →
      (∀ cDep : ℝ, ListSt cDep x → ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep K.s.b) →
      Nonempty (N K B f T w Z P.Wt p t nch n xd c)) :
    ∃ (Z : w.Lt) (v : Lv3 (prmR N S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch := by
  have hB := builtEx l hP
  obtain ⟨big, hbig⟩ := hE hB
  obtain ⟨L, hL'⟩ := hB big
  obtain ⟨hLg, he⟩ := hbig L hL'
  obtain ⟨Sp, ⟨Au⟩, ss⟩ := hL'
  obtain ⟨al⟩ := allL_nonempty l Sp Au ss hP hA
  obtain ⟨xd, hxd⟩ := hX
  obtain ⟨p, t, ⟨rx⟩, Y₁, hY₁, hz, ht⟩ := rows_ex x L hW hD hP hR fun j v h1 h2 => he j v h1 h2 v HEq.rfl
  obtain ⟨c, ⟨ne⟩, hp⟩ := core_at l Sp Au ss al hLg Y₁ hY₁ hxd t hz ht
  obtain ⟨nn⟩ := hN _ p t _ _ _ c ne hp
  have hg : GIs2 K w x.o.G := x.G_eq ▸ P.g
  exact ⟨(oL x L).Z,
    { g := hg, coh := P.coh, Wt := P.Wt, p0 := p, what₂ := t, rx := rx, nch := chD L l, n := nchD l Sp Au ss al hLg, xd := xdD L xd
      chiT := fun k v => TypesTrue.chiT_gen (fitsL L).grp k v, nx := ⟨c, nn⟩ }, rfl, keptL L l⟩

omit l in

theorem rowsAt_start : StepW Start fun K _ _ _ w => ∀ P : Pre2 K w, RowsAt P :=
  Step.trans GlobalTheory.Mem.R3.Rw.St.exists_rowsT (Step.of_all fun _ _ _ _ _ _ _ H w hs P => H w ⟨hs.1, ⟨P⟩⟩ P)

omit l in

theorem sFin : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → PrN →
    ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ArchCmp hL → SEta hL → SXd hL → SFin hL ∧ ∀ cDep : ℝ, SFinl hL cDep := by
  intro hW hD hP hL hA hE hX
  have h := rowsAt_start.and (StepW.and hE hX)
  refine ⟨h.trans (StepW.of_all ?_), fun cDep => h.trans (StepW.of_all ?_)⟩
  · intro K B f T w _ _ H P x l S Γ
    exact lv3_of_third l hW hD hP hA (H.1 P) (H.2.1 P x l) (H.2.2 P x ⟨l.toStrictHenselianAcyclic.toLI, l.b.toSeriesState⟩) S Γ (NEb hL)
      fun _ _ _ _ _ _ _ a _ => ⟨a⟩
  · intro K B f T w _ _ H P x l S Γ hp
    exact lv3_of_third l hW hD hP hA (H.1 P) (H.2.1 P x l) (H.2.2 P x ⟨l.toStrictHenselianAcyclic.toLI, l.b.toSeriesState⟩) S Γ (NEl hL cDep)
      fun _ _ _ _ _ _ _ a b => ⟨(a, ⟨b cDep hp⟩)⟩

end GlobalTheory.HeightCounting.Fin3

end

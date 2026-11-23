import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtOfExpRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnivL
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))
open GlobalTheory.SeriesTie in
private theorem gens_eq_pz (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).gens = fun i j b k Q ψ h P => (by exact ρ.gens i j b k Q ψ h P) := by
  funext i j b k Q ψ h P
  delta GlobalTheory.SeriesTie.Setup.gens GlobalTheory.ExportSeries.Base.genSet GlobalTheory.ExportSeries.Base.gen GlobalTheory.ExportSeries.Base.vecFlat
    GlobalTheory.ExportSeries.Base.vecAt GlobalTheory.ExportSeries.Frame.vec GlobalTheory.ExportSeries.Frame.placeMap
  tr_leaves x.o.Z (oL x L).Z
  kexactB (Eq.refl (ρ.gens (kc% i) (kc% j) b k (kc% Q) (kc% ψ) (kc% h) (kc% P)))
open GlobalTheory.SeriesTie in
private theorem sum_eq_pz (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).sum = fun i j b k Q ψ => (by exact ρ.sum i j b k Q ψ) := by
  funext i j b k Q ψ
  delta GlobalTheory.SeriesTie.Setup.sum GlobalTheory.ExportSeries.Base.classSum GlobalTheory.ExportSeries.Base.vecFlat
    GlobalTheory.ExportSeries.Base.vecAt GlobalTheory.ExportSeries.Frame.vec GlobalTheory.ExportSeries.Frame.placeMap
  tr_leaves x.o.Z (oL x L).Z
  kexactB (Eq.refl (ρ.sum (kc% i) (kc% j) b k (kc% Q) (kc% ψ)))
open GlobalTheory.SeriesTie in
private theorem xi_eq_pz (ρ : Setup (Dof x).ntw) (i : (DL x L).ntw.Tw) (j : Fin (DL x L).R.m) (b : Bool) :
    (setupL L ρ).xi i j b (DL x L).nexp =
      fun Q M h P a => (by with_unfolding_all exact ((ρ.xi ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (Dof x).nexp ((by with_unfolding_all exact (Q :))) M ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (P :))) (kc% a)) :)) := by
  funext Q M h P a
  delta GlobalTheory.SeriesTie.Setup.xi GlobalTheory.ExportSeries.Base.xiCoef GlobalTheory.ExportSeries.Base.xi GlobalTheory.ExportSeries.Base.vecFam
    GlobalTheory.ExportSeries.Base.vecAt GlobalTheory.ExportSeries.Frame.vec GlobalTheory.ExportSeries.Frame.placeMap
  tr_leaves x.o.Z (oL x L).Z
  kexactB (Eq.refl (ρ.xi (kc% i) (kc% j) b (Dof x).nexp (kc% Q) M (kc% h) (kc% P) (kc% a)))
open GlobalTheory.SeriesTie in
private theorem isHeckeDatum_eq_pz (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).IsHeckeDatum =
      fun i j b k P α R z => (by exact ρ.IsHeckeDatum i j b k P α R z) := by
  funext i j b k P α R z
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · exact (by with_unfolding_all exact ((⟨(d.elt), (d.reps), (d.det)⟩ : ρ.IsHeckeDatum ((i)) ((j)) b k ((P)) ((α)) ((R)) ((z))) : _))
  · exact ⟨(by with_unfolding_all exact (d.elt :)), (by with_unfolding_all exact (d.reps :)), (by with_unfolding_all exact (d.det :))⟩
section Cell
open GlobalTheory.SeriesTie
variable {ρ : Setup (Dof x).ntw} {i : (DL x L).ntw.Tw} {j : Fin (DL x L).R.m} {c : Bool}
private def rdL_pz (rd : Rd ρ (Dof x).nexp ((i)) ((j)) c) : Rd (setupL L ρ) (DL x L).nexp i j c := (rd)
private theorem rat_iff_pz (hρ : ρ.Good) (rd : Rd ρ (Dof x).nexp ((i)) ((j)) c) :
    SeriesTie.Rat (setupL_good L hρ) (@rdL_pz K B f T w P x L ρ i j c rd) ↔ SeriesTie.Rat hρ rd := by
  conv_lhs => delta SeriesTie.Rat RatBase RatTwist RatUniv
  rewrite [isDatum_eq L ρ, theta_eq L ρ, gens_eq_pz L ρ, xi_eq_pz L ρ i j c]
  kexactB (Iff.refl (SeriesTie.Rat hρ rd))
private theorem heckeTie_imp_pz {rd : Rd ρ (Dof x).nexp ((i)) ((j)) c} (h : HeckeTie rd) :
    HeckeTie (@rdL_pz K B f T w P x L ρ i j c rd) := by
  delta HeckeTie HeckeAt
  rewrite [isHeckeDatum_eq_pz L ρ]
  exact (by with_unfolding_all exact (h :))
private def cellL_pz {hρ : ρ.Good} {rd : Rd ρ (Dof x).nexp ((i)) ((j)) c} (t : CellTie hρ (Dof x).nexp rd) :
    CellTie (setupL_good L hρ) (DL x L).nexp (i := i) (j := j) (b := c) (@rdL_pz K B f T w P x L ρ i j c rd) where
  supp := (by with_unfolding_all exact (t.supp :))
  cls := (by with_unfolding_all exact (t.cls :))
  coef := (by with_unfolding_all exact (t.coef :))
  rdV := (by with_unfolding_all exact (t.rdV :))
  U_eq := (by with_unfolding_all exact (t.U_eq :))
  psiU_eq := (by with_unfolding_all exact (t.psiU_eq :))
  dat := by rewrite [isDatum_eq L ρ]; exact (by with_unfolding_all exact (t.dat :))
  dat_onto := by rewrite [isDatum_eq L ρ, theta_eq L ρ]; exact (by with_unfolding_all exact (t.dat_onto :))
  lev_iff := (by with_unfolding_all exact (t.lev_iff :))
  th_eq := by rewrite [theta_eq L ρ]; exact (by with_unfolding_all exact (t.th_eq :))
  thPsi_iff := by rewrite [gens_eq_pz L ρ]; exact (by with_unfolding_all exact (t.thPsi_iff :))
  thU_eq := by rewrite [xi_eq_pz L ρ i j c]; kexactB t.thU_eq
  thU_off := by rewrite [xi_eq_pz L ρ i j c]; kexactB t.thU_off
  rdV_inj := (by with_unfolding_all exact (t.rdV_inj :))
  mtLat_iff := kc% t.mtLat_iff
  thP_eq := by rewrite [sum_eq_pz L ρ]; exact (by with_unfolding_all exact (t.thP_eq :))
private theorem isNormL_pz (ρ : Setup (Dof x).ntw) (i : (DL x L).ntw.Tw) (j : Fin (DL x L).R.m) (c : Bool) (ν : ℂ) :
    IsNorm (datL x L).R (datL x L).geo.v₀ ((setupL L ρ).B i j c) ν ↔
      IsNorm x.m.z.R x.m.z.geo.v₀ (ρ.B ((i)) ((j)) c) ν := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨h0, e, ⟨g, c0R, c0L, hF, u, hu, hh⟩, hn⟩ := h
    exact ⟨h0, e, ⟨(by with_unfolding_all exact (g :)), (by with_unfolding_all exact (c0R :)), (by with_unfolding_all exact (c0L :)),
      kc% (famTie_imp (a := (oL x L).Z) x.o.Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF), (by with_unfolding_all exact (u :)), (by with_unfolding_all exact (hu :)), (by with_unfolding_all exact (hh :))⟩, (by with_unfolding_all exact (hn :))⟩
  · obtain ⟨h0, e, ⟨g, c0R, c0L, hF, u, hu, hh⟩, hn⟩ := h
    exact ⟨h0, e, ⟨(by with_unfolding_all exact (g :)), (by with_unfolding_all exact (c0R :)), (by with_unfolding_all exact (c0L :)),
      kc% (famTie_imp (a := x.o.Z) (oL x L).Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF), (by with_unfolding_all exact (u :)), (by with_unfolding_all exact (hu :)), (by with_unfolding_all exact (hh :))⟩, (by with_unfolding_all exact (hn :))⟩
end Cell
section Comparison₂
open GlobalTheory.SeriesTie
variable (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x)
theorem rat_setupL_iff_rat_realRd {ρ : Setup (Dof x).ntw} (h : ρ.Good) (i : (DL x L).ntw.Tw) (j : Fin (DL x L).R.m) (c : Bool) (ν : ℂ) :
    SeriesTie.Rat (setupL_good L h) (realRd (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (setupL_good L h) i j c ν) ↔
      SeriesTie.Rat h (realRd l.b.YS x.m.z.geo.v₀ h ((i)) ((j)) c ν) :=
  (by with_unfolding_all exact ((@rat_iff_pz K B f T w P x L ρ i j c h (((realRd l.b.YS x.m.z.geo.v₀ h (kc% i) (kc% j) c ν)))) : _))
theorem is_scalar_local_y_structure_of_is_scalar {ρ : Setup (Dof x).ntw} {h : ρ.Good} {i : (DL x L).ntw.Tw} {j : Fin (DL x L).R.m} {c : Bool} {ν : ℂ}
    (s : IsScalar l.b.YS x.m.z.geo.v₀ h ((i)) ((j)) c ν) :
    IsScalar (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (setupL_good L h) i j c ν :=
  ⟨s.ne, fun ⟨ν', h'⟩ => (isNormL_pz L ρ i j c ν).2 (s.norm ⟨ν', (isNormL_pz L ρ i j c ν').1 h'⟩),
    fun ⟨ν', h₁, h₂⟩ => (_root_.GlobalTheory.HeightCounting.Fin3.rat_setupL_iff_rat_realRd L l h i j c ν).2 (s.rat ⟨ν', (isNormL_pz L ρ i j c ν').1 h₁, (_root_.GlobalTheory.HeightCounting.Fin3.rat_setupL_iff_rat_realRd L l h i j c ν').1 h₂⟩)⟩
def localYStructureExportTie : ExportTie (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ where
  ρ := setupL L l.b.ser.ex.ρ
  good := setupL_good L l.b.ser.ex.good
  pin := _root_.GlobalTheory.HeightCounting.Fin3.real_pin_setup_local L l
  vec := (by with_unfolding_all exact (l.b.ser.ex.vec :))
  ν := (by with_unfolding_all exact (l.b.ser.ex.ν :))
  scalar := fun i j c => _root_.GlobalTheory.HeightCounting.Fin3.is_scalar_local_y_structure_of_is_scalar L l (h := l.b.ser.ex.good) ((by with_unfolding_all exact ((l.b.ser.ex.scalar ((i)) ((j)) c) : _)))
  tie := fun i j c => (by with_unfolding_all exact ((@cellL_pz K B f T w P x L l.b.ser.ex.ρ i j c l.b.ser.ex.good
    (((l.b.ser.ex.rd (kc% i) (kc% j) c))) (((l.b.ser.ex.tie (kc% i) (kc% j) c)))) : _))
  hecke := fun i j c => (by with_unfolding_all exact ((@heckeTie_imp_pz K B f T w P x L l.b.ser.ex.ρ i j c
    (((l.b.ser.ex.rd (kc% i) (kc% j) c))) (((l.b.ser.ex.hecke (kc% i) (kc% j) c)))) : _))
  univ := _root_.GlobalTheory.HeightCounting.Fin3.is_univ_char_local L l
private def lamL_pz (Z : GlobalTheory.LamTie.LamDat (Dof x)) : GlobalTheory.LamTie.LamDat (DL x L) :=
  ⟨(by with_unfolding_all exact ((chFr (a := x.o.Z) (oL x L).Z ((Z.C))) : _)), (by with_unfolding_all exact (Z.q0 :)), (by with_unfolding_all exact (Z.w0 :)), (by with_unfolding_all exact (Z.c :)), (by with_unfolding_all exact (Z.chi :))⟩
private theorem lamL_ok_pz {Z : GlobalTheory.LamTie.LamDat (Dof x)} (h : Z.Ok) : (lamL_pz L Z).Ok := ⟨(by with_unfolding_all exact (h.places :)), (by with_unfolding_all exact (h.aux :)), (by with_unfolding_all exact (h.big :))⟩
private theorem lamL_tie_pz {Z : GlobalTheory.LamTie.LamDat (Dof x)} (h : GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z) :
    GlobalTheory.LamTie.IsLamTieFull (DL x L).ntw (lamL_pz L Z) := (by with_unfolding_all exact (h :))
private theorem lamL_C_pz {Z : GlobalTheory.LamTie.LamDat (Dof x)} (h : Z.C = cfOf x) : (lamL_pz L Z).C = cfD x L :=
  (by with_unfolding_all exact ((congrArg (fun c : CharFrame (Dof x) => chFr (a := x.o.Z) (oL x L).Z ((c))) h) : _))
def seriesAtLocal (X : Formalism.L2.NExpTied (withLoc L)) (h : ExpRel L l.b.Bs.exp X) :
    SerAt (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (expD L X) (_root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l) (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.placeMapLocal L l) where
  ex := _root_.GlobalTheory.HeightCounting.Fin3.localYStructureExportTie L l
  bad := (by with_unfolding_all exact (l.b.ser.bad :))
  ch := (by with_unfolding_all exact (l.b.ser.ch :))
  join := fun i j b k Q ψ hA ht => (by with_unfolding_all exact ((h.reads (kc% i) (j.1 + 1) b k (kc% Q) (kc% ψ) (Nat.le_add_left _ _) (kc% j.2) (kc% hA)
    (l.b.ser.ex.ρ.ek (kc% i) b k)
    (Formalism.IndefR.Links.PolF (Dof x) (Formalism.IndefR.Links.Wc (Dof x) (kc% j)).rank (Formalism.IndefR.Links.Vc (Dof x) (kc% j)).rank)
    (fun f g => (l.b.ser.ex.tie (kc% i) (kc% j) b).rdV k (kc% Q) (kc% ψ) (kc% f)
      ((Formalism.L2.Theta.finHom _).rangeRestrict ((l.mt.ad.PV (kc% j)).ψ (kc% g))))
    (kc% (l.b.ser.join (kc% i) (kc% j) b k (kc% Q) (kc% ψ) (kc% hA) (kc% ht)))) :))
  sup := kc% l.b.ser.sup
  off := (by with_unfolding_all exact (l.b.ser.off :))
  lam := lamL_pz L l.b.ser.lam
  lam_ok := lamL_ok_pz L l.b.ser.lam_ok
  lam_teich := (by with_unfolding_all exact (l.b.ser.lam_teich :))
  lam_C := lamL_C_pz L l.b.ser.lam_C
  lam_q := (by with_unfolding_all exact (l.b.ser.lam_q :))
  lam_tie := lamL_tie_pz L l.b.ser.lam_tie
end Comparison₂
end GlobalTheory.HeightCounting.Fin3
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.series_at_local_of_exp_relation : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (X : Formalism.L2.NExpTied (withLoc L)), ExpRel L l.b.Bs.exp X → Nonempty (SerAt (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (expD L X) (_root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l) (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.placeMapLocal L l)) :=
  fun L l X h => ⟨_root_.GlobalTheory.HeightCounting.Fin3.seriesAtLocal L l X h⟩
end

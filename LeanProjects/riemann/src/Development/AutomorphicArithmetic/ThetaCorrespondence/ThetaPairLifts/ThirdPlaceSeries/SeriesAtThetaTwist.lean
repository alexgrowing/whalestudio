import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtThetaTwist
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpTh
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up.SerCp
open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.ExportSeries hiding Base
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false
section L1
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C)
private def weight_pz {n : ℕ} (x : ExportSeries.Weight a.D n) : ExportSeries.Weight b.D n where
  p := (by with_unfolding_all exact (x.p :))
  q := (by with_unfolding_all exact (x.q :))
  ap := (by with_unfolding_all exact (x.ap :))
  am := (by with_unfolding_all exact (x.am :))
  c := (by with_unfolding_all exact (x.c :))
  lam := (by with_unfolding_all exact (x.lam :))
private def twist_pz {A : Type} [CommGroup A] (x : Twist a.D A) : Twist b.D A where
  Q := (by with_unfolding_all exact (x.Q :))
  chi := (by with_unfolding_all exact (x.chi :))
  res := (by with_unfolding_all exact (x.res :))
private def typeDat_pz {r : ℕ} (x : TypeDat a.D r) : TypeDat b.D r where
  Pg := (by with_unfolding_all exact (x.Pg :))
  P := (by with_unfolding_all exact (x.P :))
  mu := (by with_unfolding_all exact (x.mu :))
private def univTw_pz {A : Type} [AddCommGroup A] (x : UnivTwist a.D A) : UnivTwist b.D A where
  del := (by with_unfolding_all exact (x.del :))
  kap := (by with_unfolding_all exact (x.kap :))
private def frame_pz {S T : HSp a.D} (x : Frame S T) : @Frame b.D ((S)) ((T)) where
  ψ := (by with_unfolding_all exact (x.ψ :))
  θ := (by with_unfolding_all exact (x.θ :))
  sT := (by with_unfolding_all exact (x.sT :))
  BS := (by with_unfolding_all exact (x.BS :))
  BT := (by with_unfolding_all exact (x.BT :))
  ΛS := (by with_unfolding_all exact (x.ΛS :))
  ΛT := (by with_unfolding_all exact (x.ΛT :))
  βS := (by with_unfolding_all exact (x.βS :))
  βT := (by with_unfolding_all exact (x.βT :))
  f₀ := (by with_unfolding_all exact (x.f₀ :))
private def base_pz {S T : HSp a.D} (x : ExportSeries.Base S T) : @ExportSeries.Base b.D ((S)) ((T)) where
  hr := (by with_unfolding_all exact (x.hr :))
  F := frame_pz b x.F
  G := (by with_unfolding_all exact ((typeDat_pz b x.G) :))
  de := twist_pz b x.de
  w := (by with_unfolding_all exact ((weight_pz b x.w) :))
  mu0 := (by with_unfolding_all exact (x.mu0 :))
  eta := (by with_unfolding_all exact (x.eta :))
private theorem twist_good_pz {A : Type} [CommGroup A] {x : Twist a.D A} (h : x.Good) : (twist_pz b x).Good :=
  { isOpen := (by with_unfolding_all exact (h.isOpen :))
    rat := (by with_unfolding_all exact (h.rat :))
    real := (by with_unfolding_all exact (h.real :))
    split := (by with_unfolding_all exact (h.split :))
    unram := (by with_unfolding_all exact (h.unram :))
    res := (by with_unfolding_all exact (h.res :)) }
private theorem weight_good_pz {n : ℕ} {x : ExportSeries.Weight a.D n} (h : x.Good) : (weight_pz b x).Good :=
  { le := (by with_unfolding_all exact (h.le :))
    lam_eq := (by with_unfolding_all exact (h.lam_eq :)) }
private theorem places_imp_pz {P Q} (h : @PlacesOK a.D P Q) : @PlacesOK b.D ((P)) ((Q)) :=
  { split := (by with_unfolding_all exact (h.split :))
    disj := (by with_unfolding_all exact (h.disj :))
    prime := (by with_unfolding_all exact (h.prime :)) }
private theorem frame_good_pz {S T : HSp a.D} {x : Frame S T} (h : x.Good) : (frame_pz b x).Good :=
  { rank_le := (by with_unfolding_all exact (h.rank_le :))
    onbS := (by with_unfolding_all exact (h.onbS :))
    cartT := (by with_unfolding_all exact (h.cartT :))
    onbT := (by with_unfolding_all exact (h.onbT :))
    sdS := (by with_unfolding_all exact (h.sdS :))
    sdT := (by with_unfolding_all exact (h.sdT :))
    frS := (by with_unfolding_all exact (h.frS :))
    frT := (by with_unfolding_all exact (h.frT :))
    vac := by
      delta IsVacO
      rewrite [thetaFun_eq a b, vacuum_eq a b]
      exact (by with_unfolding_all exact (h.vac :)) }
private theorem base_good_pz {S T : HSp a.D} {x : ExportSeries.Base S T} (h : x.Good) : (base_pz b x).Good :=
  { even := (by with_unfolding_all exact (h.even :))
    odd := (by with_unfolding_all exact (h.odd :))
    frame := (by with_unfolding_all exact ((frame_good_pz b h.frame) :))
    de := (by with_unfolding_all exact ((twist_good_pz b h.de) :))
    places := (by with_unfolding_all exact ((places_imp_pz b h.places) :))
    wt := (by with_unfolding_all exact ((weight_good_pz b h.wt) :))
    sig := (by with_unfolding_all exact (h.sig :))
    sigOK := (by with_unfolding_all exact (h.sigOK :))
    eta := (by with_unfolding_all exact (h.eta :))
    hecke := (by with_unfolding_all exact (h.hecke :))
    real := (by with_unfolding_all exact (h.real :))
    unram := (by with_unfolding_all exact (h.unram :))
    tame := (by with_unfolding_all exact (h.tame :))
    inf := (by with_unfolding_all exact (h.inf :)) }
private theorem classes_imp_pz {V : HSp a.D} {J} {I : Type} {r : I → GA a.D V} (h : IsClassSystem V J r) :
    @IsClassSystem b.D ((V)) ((J)) I ((r)) :=
  { fin := (by with_unfolding_all exact (h.fin :))
    reps := (by with_unfolding_all exact (h.reps :))
    stab := (by with_unfolding_all exact (h.stab :)) }
variable (a) in
private def placeMapB_pz : type_of% (@Frame.placeMap b.D) := @fun S T F => (by with_unfolding_all exact ((@Frame.placeMap a.D ((S)) ((T)) (((frame_pz a F)))) : _))
variable (a) in
private theorem placeMap_eq_pz : @Frame.placeMap b.D = @placeMapB_pz B C a b := by
  funext S T F e
  delta Frame.placeMap
  rewrite [placeModel_eq a b]
  exact (by with_unfolding_all exact ((Eq.refl (@placeMapB_pz B C a b S T F e)) :))
variable (a) in
private def vecAtB_pz : type_of% (@ExportSeries.Base.vecAt b.D) := @fun S T F => (by with_unfolding_all exact ((@ExportSeries.Base.vecAt a.D ((S)) ((T)) (((base_pz a F)))) : _))
variable (a) in
private theorem vecAt_eq_pz : @ExportSeries.Base.vecAt b.D = @vecAtB_pz B C a b := by
  funext S T F Q φ
  delta ExportSeries.Base.vecAt Frame.vec
  rewrite [placeMap_eq_pz a b]
  exact (by with_unfolding_all exact ((Eq.refl (@vecAtB_pz B C a b S T F Q φ)) :))
variable (a) in
private def thetaB_pz : type_of% (@ExportSeries.Base.theta b.D) := @fun S T F => (by with_unfolding_all exact ((@ExportSeries.Base.theta a.D ((S)) ((T)) (((base_pz a F)))) : _))
variable (a) in
private theorem theta_eq_pz : @ExportSeries.Base.theta b.D = @thetaB_pz B C a b := by
  funext S T F ω h
  delta ExportSeries.Base.theta ExportSeries.Base.vecBase
  rewrite [vecAt_eq_pz a b]
  exact (by with_unfolding_all exact ((Eq.refl (@thetaB_pz B C a b S T F ω h)) :))
variable (a) in
private def genSetB_pz : type_of% (@ExportSeries.Base.genSet b.D) := @fun S T F ω ψ => (by with_unfolding_all exact ((@ExportSeries.Base.genSet a.D ((S)) ((T)) (((base_pz a F))) ((ω)) (twist_pz a ψ)) : _))
variable (a) in
private theorem genSet_eq_pz : @ExportSeries.Base.genSet b.D = @genSetB_pz B C a b := by
  funext S T F ω ψ h P
  delta ExportSeries.Base.genSet ExportSeries.Base.gen ExportSeries.Base.vecFlat
  rewrite [vecAt_eq_pz a b]
  exact (by with_unfolding_all exact ((Eq.refl (@genSetB_pz B C a b S T F ω ψ h P)) :))
variable (a) in
private def classSumB_pz : type_of% (@ExportSeries.Base.classSum b.D) := @fun S T F ω ψ => (by with_unfolding_all exact ((@ExportSeries.Base.classSum a.D ((S)) ((T)) (((base_pz a F))) ((ω)) (twist_pz a ψ)) : _))
variable (a) in
private theorem classSum_eq_pz : @ExportSeries.Base.classSum b.D = @classSumB_pz B C a b := by
  funext S T F ω ψ I i h
  delta ExportSeries.Base.classSum ExportSeries.Base.vecFlat
  rewrite [vecAt_eq_pz a b]
  exact (by with_unfolding_all exact ((Eq.refl (@classSumB_pz B C a b S T F ω ψ I i h)) :))
variable (a) in
private def xiCoefB_pz : type_of% (@ExportSeries.Base.xiCoef b.D) := @fun S T F A i1 i2 ω u => (by with_unfolding_all exact ((@ExportSeries.Base.xiCoef a.D ((S)) ((T)) (((base_pz a F))) A i1 i2 ((ω)) (univTw_pz a u)) : _))
variable (a) in
private theorem xiCoef_eq_pz : @ExportSeries.Base.xiCoef b.D = @xiCoefB_pz B C a b := by
  funext S T F A i1 i2 ω u Q Φ h P c
  delta ExportSeries.Base.xiCoef ExportSeries.Base.xi ExportSeries.Base.vecFam
  rewrite [vecAt_eq_pz a b]
  exact (by with_unfolding_all exact ((Eq.refl (@xiCoefB_pz B C a b S T F A i1 i2 ω u Q Φ h P c)) :))
end L1
section L2
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C)
private def recip_pz {Ω : Type} [i1 : Field Ω] [i2 : Algebra a.D.host.E Ω] (x : Recip a.D Ω) : @Recip b.D Ω i1 ((i2)) :=
  @Recip.mk b.D Ω i1 ((by with_unfolding_all exact (i2 :))) ((by with_unfolding_all exact (x.κ :))) ((by with_unfolding_all exact (x.art :)))
private theorem recip_good_pz {Ω : Type} [i1 : Field Ω] [i2 : Algebra a.D.host.E Ω] {x : Recip a.D Ω} (h : x.Good) :
    @Recip.Good b.D Ω i1 ((i2)) (@recip_pz B C a b Ω i1 i2 x) :=
  @Recip.Good.mk b.D Ω i1 ((by with_unfolding_all exact (i2 :))) (@recip_pz B C a b Ω i1 i2 x) ((by with_unfolding_all exact (h.cont :))) ((by with_unfolding_all exact (h.rat :))) ((by with_unfolding_all exact (h.loc :))) ((by with_unfolding_all exact (h.artin :)))
private theorem choice_imp_pz {ch} (h : @IsChoice a.D ch) : @IsChoice b.D ((ch)) :=
  { pair := (by with_unfolding_all exact (h.pair :))
    one := (by with_unfolding_all exact (h.one :)) }
end L2
private abbrev lt_pz {B : Base} {C : Cols B} (c : Late B C) (n : NStage B C c.W) : Late B C := ⟨c.W, c.V, c.S, n, c.G⟩
section L2
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {c : Late B C} {a : NStage B C c.W} (b : NStage B C c.W)
section
variable {N : NData (lt_pz c a).D.R (lt_pz c a).D.host (lt_pz c a).D.what₂} {X : NTw (lt_pz c a).D.R (lt_pz c a).D.host (lt_pz c a).D.what₂ (lt_pz c a).D.LL0 N}
private def setup_pz (x : Setup X) : @Setup (lt_pz c b).D ((N)) ((X)) :=
  @Setup.mk (lt_pz c b).D ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (X :)))
    (rc := (by with_unfolding_all exact ((recip_pz (lt_pz c b) x.rc) :)))
    (ch := (by with_unfolding_all exact (x.ch :)))
    (bad := (by with_unfolding_all exact (x.bad :)))
    (e := (by with_unfolding_all exact (x.e :)))
    (ek := (by with_unfolding_all exact (x.ek :)))
    (B := fun i j s => (by with_unfolding_all exact ((base_pz (lt_pz c b) (x.B ((i)) ((j)) s)) : _)))
    (om := (by with_unfolding_all exact (x.om :)))
    (Cl := fun i j s t => x.Cl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) s (twist_pz (lt_pz c a) t))
    (finCl := fun i j s t => (by with_unfolding_all exact ((x.finCl ((i)) ((j)) s (twist_pz (lt_pz c a) t)) : _)))
    (rep := fun i j s t => (by with_unfolding_all exact ((x.rep ((i)) ((j)) s (twist_pz (lt_pz c a) t)) : _)))
    (β := (by with_unfolding_all exact (x.β :)))
    (eG := (by with_unfolding_all exact (x.eG :)))
private theorem setup_good_pz {x : Setup X} (h : x.Good) : (setup_pz (c := c) (a := a) b x).Good :=
  { rc := (by with_unfolding_all exact ((recip_good_pz (lt_pz c b) h.rc) :))
    ch := fun i => (by with_unfolding_all exact ((choice_imp_pz (lt_pz c b) (h.ch ((i)))) : _))
    bad_ne := (by with_unfolding_all exact (h.bad_ne :))
    goodSetup_bad_mem_badPlaces := (by with_unfolding_all exact (h.goodSetup_bad_mem_badPlaces :))
    goodSetup_badPlaces_conj := (by with_unfolding_all exact (h.goodSetup_badPlaces_conj :))
    goodSetup_placesOverTwo_subset := (by with_unfolding_all exact (h.goodSetup_placesOverTwo_subset :))
    goodSetup_count_eq_zero_off_badPlaces := (by with_unfolding_all exact (h.goodSetup_count_eq_zero_off_badPlaces :))
    e_LL0 := (by with_unfolding_all exact (h.e_LL0 :))
    ek_e := (by with_unfolding_all exact (h.ek_e :))
    latS := (by with_unfolding_all exact (h.latS :))
    latT := (by with_unfolding_all exact (h.latT :))
    Pg := (by with_unfolding_all exact (h.Pg :))
    base := fun i j s => (by with_unfolding_all exact ((base_good_pz (lt_pz c b) (h.base ((i)) ((j)) s)) : _))
    delta := fun i j s => (by with_unfolding_all exact ((congrArg (twist_pz (lt_pz c b)) (h.delta ((i)) ((j)) s)) : _))
    weil := fun i j s t ht => (by with_unfolding_all exact ((weilDatum_imp (lt_pz c b) _ _ _ _ _ _ (h.weil ((i)) ((j)) s (twist_pz (lt_pz c a) t) (twist_good_pz (lt_pz c a) ht))) : _))
    classes := fun i j s t ht hA => (by with_unfolding_all exact ((classes_imp_pz (lt_pz c b) (h.classes ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) s (twist_pz (lt_pz c a) t) (twist_good_pz (lt_pz c a) ht)
      ⟨(by with_unfolding_all exact ((places_imp_pz (lt_pz c a) hA.1) :)), (by with_unfolding_all exact (hA.2 :))⟩)) :)) }
private theorem isDatum_imp_pz {x : Setup X} {i j s Q g P} (h : x.IsDatum i j s Q g P) :
    (setup_pz (c := c) (a := a) b x).IsDatum ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) s ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (g :))) ((by with_unfolding_all exact (P :))) :=
  { split := (by with_unfolding_all exact (h.split :))
    off := (by with_unfolding_all exact (h.off :))
    fin := (by with_unfolding_all exact (h.fin :))
    supp := (by with_unfolding_all exact (h.supp :))
    mem := (by with_unfolding_all exact (h.mem :)) }
private theorem isHecke_imp_pz {x : Setup X} {i j s k P α R z} (h : x.IsHeckeDatum i j s k P α R z) :
    (setup_pz (c := c) (a := a) b x).IsHeckeDatum ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) s k ((by with_unfolding_all exact (P :))) ((by with_unfolding_all exact (α :))) ((by with_unfolding_all exact (R :))) ((by with_unfolding_all exact (z :))) :=
  { elt := (by with_unfolding_all exact (h.elt :))
    reps := (by with_unfolding_all exact (h.reps :))
    det := (by with_unfolding_all exact (h.det :)) }
end
variable (a) in
private def isDatumB_pz : type_of% (@Setup.IsDatum (lt_pz c b).D) := @fun N X ρ => (by with_unfolding_all exact ((@Setup.IsDatum (lt_pz c a).D ((N)) ((X)) (((setup_pz (c := c) (a := b) a ρ)))) : _))
variable (a) in
private theorem isDatum_eq_pz : @Setup.IsDatum (lt_pz c b).D = @isDatumB_pz B C c a b := by
  funext N X ρ i j s Q g P
  exact propext ⟨fun h => (by with_unfolding_all exact ((isDatum_imp_pz (c := c) (a := b) a h) :)), fun h => (by with_unfolding_all exact ((isDatum_imp_pz (c := c) (a := a) b (x := setup_pz (c := c) (a := b) a ρ) (i := (i)) (j := (j)) (s := s) (Q := (Q)) (g := (g)) (P := (P)) ((h))) : _))⟩
variable (a) in
private def isHeckeB_pz : type_of% (@Setup.IsHeckeDatum (lt_pz c b).D) := @fun N X ρ => (by with_unfolding_all exact ((@Setup.IsHeckeDatum (lt_pz c a).D ((N)) ((X)) (((setup_pz (c := c) (a := b) a ρ)))) : _))
variable (a) in
private theorem isHecke_eq_pz : @Setup.IsHeckeDatum (lt_pz c b).D = @isHeckeB_pz B C c a b := by
  funext N X ρ i j s k P α R z
  exact propext ⟨fun h => (by with_unfolding_all exact ((isHecke_imp_pz (c := c) (a := b) a h) :)), fun h => (by with_unfolding_all exact ((isHecke_imp_pz (c := c) (a := a) b (x := setup_pz (c := c) (a := b) a ρ) (i := (i)) (j := (j)) (s := s) (k := k) (P := (P)) (α := (α)) (R := (R)) (z := (z)) ((h))) : _))⟩
section
variable {N : NData (lt_pz c a).D.R (lt_pz c a).D.host (lt_pz c a).D.what₂} {X : NTw (lt_pz c a).D.R (lt_pz c a).D.host (lt_pz c a).D.what₂ (lt_pz c a).D.LL0 N} {ρ : Setup X}
  {Y : NExp (lt_pz c a).D.R (lt_pz c a).D.host (lt_pz c a).D.what₂ (lt_pz c a).D.LL0 N X} {i : X.Tw} {j : Fin (lt_pz c a).D.R.m} {s : Bool} {rd : Rd ρ Y i j s}
private def cell_pz {hρ : ρ.Good} (x : CellTie hρ Y rd) :
    @CellTie (lt_pz c b).D ((N)) ((X)) (setup_pz (c := c) (a := a) b ρ) (setup_good_pz (c := c) (a := a) b hρ) ((Y)) ((i)) ((j)) s ((rd)) :=
  @CellTie.mk (lt_pz c b).D ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (X :))) (setup_pz (c := c) (a := a) b ρ) (setup_good_pz (c := c) (a := a) b hρ) ((by with_unfolding_all exact (Y :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) s ((by with_unfolding_all exact (rd :)))
    (supp := (by with_unfolding_all exact (x.supp :)))
    (cls := (by with_unfolding_all exact (x.cls :)))
    (coef := (by with_unfolding_all exact (x.coef :)))
    (rdV := (by with_unfolding_all exact (x.rdV :)))
    (U_eq := (by with_unfolding_all exact (x.U_eq :)))
    (psiU_eq := (by with_unfolding_all exact (x.psiU_eq :)))
    (dat := fun d => (by with_unfolding_all exact ((isDatum_imp_pz (c := c) (a := a) b (x.dat ((d)))) : _)))
    (dat_onto := by delta Setup.theta; rewrite [isDatum_eq_pz (c := c) a b, theta_eq_pz (lt_pz c a) (lt_pz c b)]; exact (by with_unfolding_all exact (x.dat_onto :)))
    (lev_iff := (by with_unfolding_all exact (x.lev_iff :)))
    (th_eq := by delta Setup.theta; rewrite [theta_eq_pz (lt_pz c a) (lt_pz c b)]; exact (by with_unfolding_all exact (x.th_eq :)))
    (thPsi_iff := by delta Setup.gens; rewrite [genSet_eq_pz (lt_pz c a) (lt_pz c b)]; exact (by with_unfolding_all exact (x.thPsi_iff :)))
    (thU_eq := by delta Setup.xi; rewrite [xiCoef_eq_pz (lt_pz c a) (lt_pz c b)]; exact (by with_unfolding_all exact (x.thU_eq :)))
    (thU_off := by delta Setup.xi; rewrite [xiCoef_eq_pz (lt_pz c a) (lt_pz c b)]; exact (by with_unfolding_all exact (x.thU_off :)))
    (rdV_inj := (by with_unfolding_all exact (x.rdV_inj :)))
    (mtLat_iff := (by with_unfolding_all exact (x.mtLat_iff :)))
    (thP_eq := by delta Setup.sum; rewrite [classSum_eq_pz (lt_pz c a) (lt_pz c b)]; exact (by with_unfolding_all exact (x.thP_eq :)))
private theorem hecke_imp_pz (h : HeckeTie rd) :
    @HeckeTie (lt_pz c b).D ((N)) ((X)) (setup_pz (c := c) (a := a) b ρ) ((Y)) ((i)) ((j)) s ((rd)) := by
  delta HeckeTie HeckeAt
  rewrite [isHecke_eq_pz (c := c) a b]
  exact (by with_unfolding_all exact (h :))
private theorem rat_imp_pz {hρ : ρ.Good} (h : SeriesTie.Rat hρ rd) :
    @SeriesTie.Rat (lt_pz c b).D ((N)) ((X)) (setup_pz (c := c) (a := a) b ρ) (setup_good_pz (c := c) (a := a) b hρ) ((Y)) ((i)) ((j)) s ((rd)) := by
  delta SeriesTie.Rat RatBase RatTwist RatUniv Setup.theta Setup.gens Setup.xi
  rewrite [isDatum_eq_pz (c := c) a b, theta_eq_pz (lt_pz c a) (lt_pz c b), genSet_eq_pz (lt_pz c a) (lt_pz c b), xiCoef_eq_pz (lt_pz c a) (lt_pz c b)]
  exact (by with_unfolding_all exact (h :))
end
end L2
section L3
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {c : Late B C} {a : NStage B C c.W} (b : NStage B C c.W)
  {Γ : Type} [i1 : Group Γ] [i2 : Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 (lt_pz c a).D.what₂.LL Γ Pl0 I0 (List ℕ) T (lt_pz c a).D.R.m} {Ks : Type} [i3 : Field Ks] [i4 : NumberField Ks]
  [iK : Algebra Ks (lt_pz c a).D.what₂.LL] {Rl : RealDat3 (lt_pz c a).D A3 Ks}
  {v₀ : ∀ (j : Fin (lt_pz c a).D.R.m) (σ : (lt_pz c a).D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec} {j : Fin (lt_pz c a).D.R.m}
  {X : ExportSeries.Base (Vc (lt_pz c a).D j) (Wc (lt_pz c a).D j)} {ν : ℂ}
private theorem norm_to_pz (h : IsNorm Rl v₀ X ν) :
    @IsNorm (lt_pz c b).D Γ i1 i2 Pl0 I0 T (famInThreeCoefficientChange (a := lt_pz c a) (lt_pz c b) A3) Ks i3 i4 (alg (a := lt_pz c a) (lt_pz c b) iK)
      (real3 (a := lt_pz c a) (lt_pz c b) Rl) ((by with_unfolding_all exact (v₀ :))) ((by with_unfolding_all exact (j :))) ((by with_unfolding_all exact ((base_pz (a := lt_pz c a) (lt_pz c b) X) :))) ν := by
  delta IsNorm IsScale
  rewrite [famTie_eq (lt_pz c a) (lt_pz c b)]
  kexactB h
private theorem norm_from_pz
    (h : @IsNorm (lt_pz c b).D Γ i1 i2 Pl0 I0 T (famInThreeCoefficientChange (a := lt_pz c a) (lt_pz c b) A3) Ks i3 i4 (alg (a := lt_pz c a) (lt_pz c b) iK)
      (real3 (a := lt_pz c a) (lt_pz c b) Rl) ((by with_unfolding_all exact (v₀ :))) ((by with_unfolding_all exact (j :))) ((by with_unfolding_all exact ((base_pz (a := lt_pz c a) (lt_pz c b) X) :))) ν) : IsNorm Rl v₀ X ν := by
  delta IsNorm IsScale at h
  rewrite [famTie_eq (lt_pz c a) (lt_pz c b)] at h
  kexactB h
end L3
section L4
open GlobalTheory.SeriesTie
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp)
private def nTh_pz : NStage B w.C x.o.Z.W := (by with_unfolding_all exact ((nTw x (thTw (Dof x) th)) :))
def thetaTwistSetup : Setup (w.st (oTw x (thTw (Dof x) th)).Z).toD7.ntw :=
  (by with_unfolding_all exact ((setup_pz (c := x.o.Z) (a := x.o.Z.N) (nTh_pz x th) l.b.ser.ex.ρ) :))
theorem theta_twist_rho_good : (_root_.GlobalTheory.HeightCounting.Up.SerCp.thetaTwistSetup x l th).Good :=
  (by with_unfolding_all exact ((setup_good_pz (c := x.o.Z) (a := x.o.Z.N) (nTh_pz x th) l.b.ser.ex.good) :))
theorem real_pin_theta_twist_rho : RealPin (datTw x (thTw (Dof x) th)).R (datTw x (thTw (Dof x) th)).cG (_root_.GlobalTheory.HeightCounting.Up.SerCp.thetaTwistSetup x l th) :=
  have h := l.b.ser.ex.pin
  { psi := (by with_unfolding_all exact (h.psi :))
    inf := (by with_unfolding_all exact (h.inf :))
    cartT := (by with_unfolding_all exact (h.cartT :))
    onbS := (by with_unfolding_all exact (h.onbS :))
    onbT := (by with_unfolding_all exact (h.onbT :))
    latS := (by with_unfolding_all exact (h.latS :))
    latT := (by with_unfolding_all exact (h.latT :))
    frS := (by with_unfolding_all exact (h.frS :))
    frT := (by with_unfolding_all exact (h.frT :))
    vac := (by with_unfolding_all exact (h.vac :))
    Pg := (by with_unfolding_all exact (h.Pg :))
    grp := (by with_unfolding_all exact (h.grp :))
    mu0 := (by with_unfolding_all exact (h.mu0 :))
    eta := (by with_unfolding_all exact (h.eta :))
    delta := (by with_unfolding_all exact (h.delta :))
    deltaPl := (by with_unfolding_all exact (h.deltaPl :))
    ap := (by with_unfolding_all exact (h.ap :))
    am := (by with_unfolding_all exact (h.am :)) }
theorem is_norm_theta_twist_iff (i j s ν) : IsNorm (datTw x (thTw (Dof x) th)).R (datTw x (thTw (Dof x) th)).geo.v₀ ((_root_.GlobalTheory.HeightCounting.Up.SerCp.thetaTwistSetup x l th).B i j s) ν ↔
    IsNorm x.m.z.R x.m.z.geo.v₀ (l.b.ser.ex.ρ.B ((i)) ((j)) s) ν :=
  ⟨fun h => (by with_unfolding_all exact ((norm_from_pz (c := x.o.Z) (a := x.o.Z.N) (nTh_pz x th) (iK := x.m.z.alg) (Rl := x.m.z.R) (v₀ := x.m.z.geo.v₀)
      (X := l.b.ser.ex.ρ.B ((i)) ((j)) s) (ν := ν) ((h))) : _)),
    fun h => (by with_unfolding_all exact ((norm_to_pz (c := x.o.Z) (a := x.o.Z.N) (nTh_pz x th) (iK := x.m.z.alg) h) :))⟩
theorem series_rat_theta_twist_iff (i j s ν) :
    SeriesTie.Rat (_root_.GlobalTheory.HeightCounting.Up.SerCp.theta_twist_rho_good x l th) (realRd (_root_.GlobalTheory.HeightCounting.Up.ysTh_alt x l th) (datTw x (thTw (Dof x) th)).geo.v₀ (_root_.GlobalTheory.HeightCounting.Up.SerCp.theta_twist_rho_good x l th) i j s ν) ↔
      SeriesTie.Rat l.b.ser.ex.good (realRd l.b.YS x.m.z.geo.v₀ l.b.ser.ex.good ((i)) ((j)) s ν) :=
  ⟨fun h => (by with_unfolding_all exact ((rat_imp_pz (c := x.o.Z) (a := nTh_pz x th) x.o.Z.N h) :)),
    fun h => (by with_unfolding_all exact ((rat_imp_pz (c := x.o.Z) (a := x.o.Z.N) (nTh_pz x th) h) :))⟩
theorem is_scalar_theta_twist_ys (i j s) : IsScalar (_root_.GlobalTheory.HeightCounting.Up.ysTh_alt x l th) (datTw x (thTw (Dof x) th)).geo.v₀ (_root_.GlobalTheory.HeightCounting.Up.SerCp.theta_twist_rho_good x l th) i j s
    (l.b.ser.ex.ν ((i)) ((j)) s) :=
  have h := l.b.ser.ex.scalar ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) s
  ⟨h.ne, fun h' => (_root_.GlobalTheory.HeightCounting.Up.SerCp.is_norm_theta_twist_iff x l th i j s _).2 (h.norm (h'.imp fun ν => (_root_.GlobalTheory.HeightCounting.Up.SerCp.is_norm_theta_twist_iff x l th i j s ν).1)),
    fun h' => (_root_.GlobalTheory.HeightCounting.Up.SerCp.series_rat_theta_twist_iff x l th i j s _).2 (h.rat (h'.imp fun ν k => ⟨(_root_.GlobalTheory.HeightCounting.Up.SerCp.is_norm_theta_twist_iff x l th i j s ν).1 k.1, (_root_.GlobalTheory.HeightCounting.Up.SerCp.series_rat_theta_twist_iff x l th i j s ν).1 k.2⟩))⟩
def thetaTwistExportTie : ExportTie (_root_.GlobalTheory.HeightCounting.Up.ysTh_alt x l th) (datTw x (thTw (Dof x) th)).geo.v₀ where
  ρ := _root_.GlobalTheory.HeightCounting.Up.SerCp.thetaTwistSetup x l th
  good := _root_.GlobalTheory.HeightCounting.Up.SerCp.theta_twist_rho_good x l th
  pin := _root_.GlobalTheory.HeightCounting.Up.SerCp.real_pin_theta_twist_rho x l th
  vec := (by with_unfolding_all exact (l.b.ser.ex.vec :))
  ν := (by with_unfolding_all exact (l.b.ser.ex.ν :))
  scalar := (by with_unfolding_all exact ((_root_.GlobalTheory.HeightCounting.Up.SerCp.is_scalar_theta_twist_ys x l th) :))
  tie := fun i j s => (by with_unfolding_all exact ((cell_pz (c := x.o.Z) (a := x.o.Z.N) (nTh_pz x th) (l.b.ser.ex.tie ((i)) ((j)) s)) : _))
  hecke := fun i j s => (by with_unfolding_all exact ((hecke_imp_pz (c := x.o.Z) (a := x.o.Z.N) (nTh_pz x th) (l.b.ser.ex.hecke ((i)) ((j)) s)) : _))
  univ := (by with_unfolding_all exact (l.b.ser.ex.univ :))
theorem series_theta_twist_exists : Nonempty (SerAt (_root_.GlobalTheory.HeightCounting.Up.ysTh_alt x l th) (datTw x (thTw (Dof x) th)).geo.v₀ (_root_.GlobalTheory.HeightCounting.Up.exponentOfTheta x l th) (_root_.GlobalTheory.HeightCounting.Up.rowPsiOfTheta x l.toLI th)
    (TC.cf w.I w.l (oTw x (thTw (Dof x) th)).Z) l.Pq) := by
  obtain ⟨Z, h1, h2, h3, h4, h5⟩ := lam_thTw th ⟨l.b.ser.lam, l.b.ser.lam_ok, l.b.ser.lam_teich, l.b.ser.lam_C, l.b.ser.lam_q,
    l.b.ser.lam_tie⟩
  exact ⟨⟨_root_.GlobalTheory.HeightCounting.Up.SerCp.thetaTwistExportTie x l th, (by with_unfolding_all exact (l.b.ser.bad :)), (by with_unfolding_all exact (l.b.ser.ch :)), (by with_unfolding_all exact (l.b.ser.join :)), (by with_unfolding_all exact (l.b.ser.sup :)), (by with_unfolding_all exact (l.b.ser.off :)), (by with_unfolding_all exact (Z :)), (by with_unfolding_all exact (h1 :)), (by with_unfolding_all exact (h2 :)),
    (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact (h4 :)), (by with_unfolding_all exact (h5 :))⟩⟩
end L4
end GlobalTheory.HeightCounting.Up.SerCp
end
theorem _root_.GlobalTheory.T.series_at_theta_twist_ys_exp : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp), Nonempty (SerAt (_root_.GlobalTheory.HeightCounting.Up.ysTh_alt x l th) (datTw x (thTw (Dof x) th)).geo.v₀ (_root_.GlobalTheory.HeightCounting.Up.exponentOfTheta x l th) (_root_.GlobalTheory.HeightCounting.Up.rowPsiOfTheta x l.toLI th) (TC.cf w.I w.l (oTw x (thTw (Dof x) th)).Z) l.Pq) :=
  fun _ _ _ _ _ _ _ x l th => _root_.GlobalTheory.HeightCounting.Up.SerCp.series_theta_twist_exists x l th
end

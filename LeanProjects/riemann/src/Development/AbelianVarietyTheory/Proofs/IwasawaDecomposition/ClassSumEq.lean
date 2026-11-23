import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr Formalism.IndefR.Datum
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.SerCopy

variable {B : GlobalTheory.Mem.Base} {C : Cols B} {a : Late B C} (b : Late B C)

def twT {A : Type} [CommGroup A] (t : Twist a.D A) : Twist b.D A := ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

def unT {A : Type} [AddCommGroup A] (t : UnivTwist a.D A) : UnivTwist b.D A := ⟨(by with_unfolding_all exact (t.del :)), (by with_unfolding_all exact (t.kap :))⟩

def wtT {n : ℕ} (w : ExportSeries.Weight a.D n) : ExportSeries.Weight b.D n := ⟨(by with_unfolding_all exact (w.p :)), (by with_unfolding_all exact (w.q :)), (by with_unfolding_all exact (w.ap :)), (by with_unfolding_all exact (w.am :)), (by with_unfolding_all exact (w.c :)), (by with_unfolding_all exact (w.lam :))⟩

def tyT {n : ℕ} (g : TypeDat a.D n) : TypeDat b.D n := ⟨(by with_unfolding_all exact (g.Pg :)), (by with_unfolding_all exact (g.P :)), (by with_unfolding_all exact (g.mu :))⟩

variable {S T : HSp a.D}

def frT (F : Frame S T) : @Frame b.D ((S)) ((T)) :=
  ⟨(by with_unfolding_all exact (F.ψ :)), (by with_unfolding_all exact (F.θ :)), (by with_unfolding_all exact (F.sT :)), (by with_unfolding_all exact (F.BS :)), (by with_unfolding_all exact (F.BT :)), (by with_unfolding_all exact (F.ΛS :)), (by with_unfolding_all exact (F.ΛT :)), (by with_unfolding_all exact (F.βS :)), (by with_unfolding_all exact (F.βT :)), (by with_unfolding_all exact (F.f₀ :))⟩

def baT (X : ExportSeries.Base S T) : @ExportSeries.Base b.D ((S)) ((T)) :=
  ⟨(by with_unfolding_all exact (X.hr :)), frT b X.F, (by with_unfolding_all exact ((tyT b X.G) :)), twT b X.de, (by with_unfolding_all exact ((wtT b X.w) :)), (by with_unfolding_all exact (X.mu0 :)), (by with_unfolding_all exact (X.eta :))⟩

theorem twGood {A : Type} [CommGroup A] {t : Twist a.D A} (h : t.Good) : (twT b t).Good :=
  ⟨(by with_unfolding_all exact (h.isOpen :)), (by with_unfolding_all exact (h.rat :)), (by with_unfolding_all exact (h.real :)), (by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.unram :)), (by with_unfolding_all exact (h.res :))⟩

theorem placesOK {Pg Q : Finset (Pl a.D.host.E)} (h : PlacesOK (D := a.D) Pg Q) : PlacesOK (D := b.D) ((by with_unfolding_all exact (Pg :))) ((by with_unfolding_all exact (Q :))) :=
  ⟨(by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.disj :)), (by with_unfolding_all exact (h.prime :))⟩

theorem frGood {F : Frame S T} (h : F.Good) : (frT b F).Good :=
  ⟨(by with_unfolding_all exact (h.rank_le :)), (by with_unfolding_all exact (h.onbS :)), (by with_unfolding_all exact (h.cartT :)), (by with_unfolding_all exact (h.onbT :)), (by with_unfolding_all exact (h.sdS :)), (by with_unfolding_all exact (h.sdT :)), (by with_unfolding_all exact (h.frS :)), (by with_unfolding_all exact (h.frT :)),
    ⟨(by with_unfolding_all exact (h.vac.1 :)), by rewrite [vacuum_eq a b, thetaFun_eq a b]; exact (by with_unfolding_all exact (h.vac.2 :))⟩⟩

theorem baGood {X : ExportSeries.Base S T} (h : X.Good) : (baT b X).Good where
  even := (by with_unfolding_all exact (h.even :))
  odd := (by with_unfolding_all exact (h.odd :))
  frame := frGood b h.frame
  de := twGood b h.de
  places := (by with_unfolding_all exact ((placesOK b h.places) :))
  wt := ⟨(by with_unfolding_all exact (h.wt.le :)), (by with_unfolding_all exact (h.wt.lam_eq :))⟩
  sig := (by with_unfolding_all exact (h.sig :))
  sigOK := (by with_unfolding_all exact (h.sigOK :))
  eta := (by with_unfolding_all exact (h.eta :))
  hecke := (by with_unfolding_all exact (h.hecke :))
  real := (by with_unfolding_all exact (h.real :))
  unram := (by with_unfolding_all exact (h.unram :))
  tame := (by with_unfolding_all exact (h.tame :))
  inf := (by with_unfolding_all exact (h.inf :))

theorem baWeil {X : ExportSeries.Base S T} {ν ω} (h : X.IsWeil ν ω) : (baT b X).IsWeil ((ν)) ((ω)) :=
  (by with_unfolding_all exact ((weilDatum_imp b _ _ _ _ _ _ h) :))

theorem baAdm {X : ExportSeries.Base S T} {Q} (h : X.admitted Q) : (baT b X).admitted ((Q)) :=
  ⟨(by with_unfolding_all exact ((placesOK b h.1) :)), (by with_unfolding_all exact (h.2 :))⟩

theorem classSys {V : HSp a.D} {J} {I : Type} {r : I → GA a.D V} (h : IsClassSystem V J r) :
    @IsClassSystem b.D ((V)) ((J)) I ((r)) := ⟨(h.fin), (h.reps), (h.stab)⟩

theorem placeMap_eq (F : Frame S T) : (frT b F).placeMap = (F.placeMap) := by
  funext e
  delta Frame.placeMap
  rewrite [placeModel_eq a b]
  exact (by with_unfolding_all exact ((Eq.refl (F.placeMap ((by with_unfolding_all exact (e :))))) :))

open Classical in
theorem vecAt_eq (X : ExportSeries.Base S T) : (baT b X).vecAt = (X.vecAt) := by
  delta ExportSeries.Base.vecAt Frame.vec
  rewrite [show (baT b X).F.placeMap = (by with_unfolding_all exact (X.F.placeMap :)) from (by with_unfolding_all exact ((placeMap_eq b X.F) :))]
  exact (by with_unfolding_all exact ((Eq.refl X.vecAt) :))

theorem theta_eq (X : ExportSeries.Base S T) : (baT b X).theta = (X.theta) := by
  delta ExportSeries.Base.theta ExportSeries.Base.vecBase
  rewrite [vecAt_eq b X]
  exact (by with_unfolding_all exact ((Eq.refl X.theta) :))

theorem genSet_eq (X : ExportSeries.Base S T) (ω) (t : Twist a.D Circle) :
    (baT b X).genSet (((ω : PairRep S T))) (twT b t) = ((X.genSet ω t : GA b.D S → PolF b.D T.rank S.rank → Set (GA b.D T → ℂ))) := by
  delta ExportSeries.Base.genSet ExportSeries.Base.gen ExportSeries.Base.vecFlat
  rewrite [vecAt_eq b X]
  exact (by with_unfolding_all exact ((Eq.refl (X.genSet ω t)) :))

theorem xiCoef_eq {A : Type} [AddCommGroup A] [Fintype A] (X : ExportSeries.Base S T) (ω) (u : UnivTwist a.D A) :
    (baT b X).xiCoef (((ω : PairRep S T))) (unT b u) = ((X.xiCoef ω u : (Q : Finset (Pl b.D.host.E)) → ((PP : Pl b.D.host.E) → A → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) → GA b.D S → PolF b.D T.rank S.rank → (↥Q → A) → GA b.D T → ℂ)) := by
  delta ExportSeries.Base.xiCoef ExportSeries.Base.xi ExportSeries.Base.vecFam
  rewrite [vecAt_eq b X]
  exact (by with_unfolding_all exact ((Eq.refl (X.xiCoef ω u)) :))

theorem classSum_eq (X : ExportSeries.Base S T) (ω) (t : Twist a.D Circle) {I : Type} [Fintype I] (r : I → GA a.D S) :
    (baT b X).classSum (((ω : PairRep S T))) (twT b t) (I := I) (((r : I → GA b.D S))) = ((X.classSum ω t r : (↥(Bridge.Gf S) → PolF b.D T.rank S.rank) →ₗ[ℂ] GA b.D T → ℂ)) := by
  delta ExportSeries.Base.classSum ExportSeries.Base.vecFlat
  rewrite [vecAt_eq b X]
  exact (by with_unfolding_all exact ((Eq.refl (X.classSum ω t r)) :))

def rcT {Ω : Type} [Field Ω] [i : Algebra a.D.host.E Ω] (r : Recip a.D Ω) : @Recip b.D Ω _ ((i)) :=
  @Recip.mk b.D Ω _ ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (r.κ :))) ((by with_unfolding_all exact (r.art :)))

theorem rcGood {Ω : Type} [Field Ω] [i : Algebra a.D.host.E Ω] {r : Recip a.D Ω} (h : r.Good) :
    @Recip.Good b.D Ω _ ((i)) (@rcT B C a b Ω _ i r) := @Recip.Good.mk b.D Ω _ ((i)) _ ((by with_unfolding_all exact (h.cont :))) ((by with_unfolding_all exact (h.rat :))) ((by with_unfolding_all exact (h.loc :))) ((by with_unfolding_all exact (h.artin :)))

theorem choiceT {ch : Set (Pl a.D.host.E)} (h : IsChoice (D := a.D) ch) : IsChoice (D := b.D) ((by with_unfolding_all exact (ch :))) :=
  ⟨(by with_unfolding_all exact (h.pair :)), (by with_unfolding_all exact (h.one :))⟩

section Setup

structure Oth {B : GlobalTheory.Mem.Base} {C : Cols B} (W : RowsRest B C) where
  V : DivStage B C W
  S : SStage B C W
  N : NStage B C W
  G : GJStage B C

variable {B : GlobalTheory.Mem.Base} {C : Cols B} {W : RowsRest B C}

def Oth.L (o : Oth W) : Late B C := ⟨W, o.V, o.S, o.N, o.G⟩

def Oth.of (a : Late B C) : Oth a.W := ⟨a.V, a.S, a.N, a.G⟩

variable {o : Oth W} (o' : Oth W) {N : NData o.L.D.R o.L.D.host o.L.D.what₂} {X : NTw o.L.D.R o.L.D.host o.L.D.what₂ o.L.D.LL0 N}

def seT (ρ : Setup X) : @Setup o'.L.D ((N)) ((X)) :=
  @Setup.mk o'.L.D ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (X :))) ((by with_unfolding_all exact ((rcT o'.L ρ.rc) :))) ((by with_unfolding_all exact (ρ.ch :))) ((by with_unfolding_all exact (ρ.bad :))) ((by with_unfolding_all exact (ρ.e :))) ((by with_unfolding_all exact (ρ.ek :)))
    (fun i j b => (by with_unfolding_all exact ((baT o'.L (ρ.B ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)) :))) ((by with_unfolding_all exact (ρ.om :)))
    (fun i j b t => ρ.Cl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twT o.L t)) (fun i j b t => ρ.finCl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twT o.L t))
    (fun i j b t => (by with_unfolding_all exact ((ρ.rep ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twT o.L t)) :))) ((by with_unfolding_all exact (ρ.β :))) ((by with_unfolding_all exact (ρ.eG :)))

variable {ρ : Setup X}

theorem seGood (h : ρ.Good) : (seT o' ρ).Good where
  rc := (by with_unfolding_all exact ((rcGood o'.L h.rc) :))
  ch := fun i => (by with_unfolding_all exact ((choiceT o'.L (h.ch ((by with_unfolding_all exact (i :))))) :))
  bad_ne := (by with_unfolding_all exact (h.bad_ne :))
  goodSetup_bad_mem_badPlaces := (by with_unfolding_all exact (h.goodSetup_bad_mem_badPlaces :))
  goodSetup_badPlaces_conj := (by with_unfolding_all exact (h.goodSetup_badPlaces_conj :))
  goodSetup_placesOverTwo_subset := (by with_unfolding_all exact (h.goodSetup_placesOverTwo_subset :))
  goodSetup_count_eq_zero_off_badPlaces := (by with_unfolding_all exact (h.goodSetup_count_eq_zero_off_badPlaces :))
  e_LL0 := (by with_unfolding_all exact (h.e_LL0 :))
  ek_e := (by with_unfolding_all exact (h.ek_e :))
  base := fun i j b => (by with_unfolding_all exact ((baGood o'.L (h.base ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)) :))
  latS := (by with_unfolding_all exact (h.latS :))
  latT := (by with_unfolding_all exact (h.latT :))
  Pg := (by with_unfolding_all exact (h.Pg :))
  delta := fun i j b => (by with_unfolding_all exact ((congrArg (twT o'.L) (h.delta ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)) :))
  weil := fun i j b t ht => (by with_unfolding_all exact ((baWeil o'.L (h.weil ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twT o.L t) (twGood o.L ht))) :))
  classes := fun i j b t ht ha => (by with_unfolding_all exact ((classSys o'.L (h.classes ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twT o.L t) (twGood o.L ht) ((by with_unfolding_all exact ((baAdm o.L ha) :))))) :))

variable (ρ) (i : X.Tw) (j : Fin o.L.D.R.m) (b : Bool)

theorem se_theta : (seT o' ρ).theta ((i)) ((j)) b = (ρ.theta i j b) := by
  funext h P
  have e : @Eq (type_of% (ρ.B i j b).theta) ((by with_unfolding_all exact ((baT o'.L (ρ.B i j b)).theta :))) (ρ.B i j b).theta :=
    (by with_unfolding_all exact ((theta_eq o'.L (ρ.B i j b)) :))
  exact (by with_unfolding_all exact ((congrArg (fun t : type_of% (ρ.B i j b).theta => t (ρ.om i j b 1) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (P :)))) e) :))

theorem se_gens : (seT o' ρ).gens ((i)) ((j)) b = (ρ.gens i j b) := by
  funext k Q ψ
  exact (by with_unfolding_all exact ((genSet_eq o'.L (ρ.B i j b) (ρ.om i j b 1) (ρ.tw i b k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))))) :))

theorem se_sum : (seT o' ρ).sum ((i)) ((j)) b = (ρ.sum i j b) := by
  funext k Q ψ
  exact (by with_unfolding_all exact ((classSum_eq o'.L (ρ.B i j b) (ρ.om i j b (ρ.tw i b k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :)))).chi) (ρ.tw i b k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))))
    (ρ.rep i j b (ρ.tw i b k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :)))))) :))

theorem se_xi (Y : NExp o.L.D.R o.L.D.host o.L.D.what₂ o.L.D.LL0 N X) :
    (seT o' ρ).xi ((i)) ((j)) b ((Y)) = (ρ.xi i j b Y) := by
  funext Q M
  exact (by with_unfolding_all exact ((congrFun (congrFun (xiCoef_eq o'.L (ρ.B i j b) (ρ.om i j b 1) (univOf Y i (admissibleConjugatePairPlaces X i ((by with_unfolding_all exact (Q :))) M) M ρ.rc))
    ((by with_unfolding_all exact ((half (ρ.ch i) (admissibleConjugatePairPlaces X i ((Q)) M)) : _))))
    ((by with_unfolding_all exact ((ExportSeries.Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i ((Q)) M) M ρ.rc) (ρ.β j)) : _)))) :))

variable {ρ i j b}

theorem se_datum {s h P} (d : ρ.IsDatum i j b s h P) : (seT o' ρ).IsDatum ((i)) ((j)) b ((s)) ((h)) ((P)) :=
  ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (d.mem :))⟩

theorem se_datum' {s h P} (d : (seT o' ρ).IsDatum ((i)) ((j)) b s h P) : ρ.IsDatum i j b ((s)) ((h)) ((P)) :=
  ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (d.mem :))⟩

theorem se_hk {k P α R z} (d : ρ.IsHeckeDatum i j b k P α R z) :
    (seT o' ρ).IsHeckeDatum ((i)) ((j)) b k ((P)) ((α)) ((R)) ((z)) := ⟨(d.elt), (d.reps), (d.det)⟩

theorem se_hk' {k P α R z} (d : (seT o' ρ).IsHeckeDatum ((i)) ((j)) b k P α R z) :
    ρ.IsHeckeDatum i j b k ((P)) ((α)) ((R)) ((z)) := ⟨(d.elt), (d.reps), (d.det)⟩

variable {Y : NExp o.L.D.R o.L.D.host o.L.D.what₂ o.L.D.LL0 N X}

def rdT (rd : Rd ρ Y i j b) : @Rd o'.L.D ((N)) ((X)) (@seT B C W o o' N X ρ) ((Y)) ((i)) ((j)) b := (rd)

variable {rd : Rd ρ Y i j b}

theorem heckeTieT (h : HeckeTie rd) : @HeckeTie o'.L.D ((N)) ((X)) (@seT B C W o o' N X ρ) ((Y)) ((i)) ((j)) b (@rdT B C W o o' N X ρ i j b Y rd) := fun k P hk f hg α R z d =>
  (by with_unfolding_all exact ((h k ((by with_unfolding_all exact (P :))) ((by with_unfolding_all exact (hk :))) ((by with_unfolding_all exact (f :))) (hg.elim fun g e => ⟨(by with_unfolding_all exact (g :)), fun α R z d => (by with_unfolding_all exact ((e _ _ _ (se_hk o' d)) :))⟩) ((by with_unfolding_all exact (α :))) ((by with_unfolding_all exact (R :))) ((by with_unfolding_all exact (z :)))
    (se_hk' o' d)) :))

variable {hρ : ρ.Good}

theorem ratT (h : SeriesTie.Rat hρ rd) : SeriesTie.Rat (@seGood B C W o o' N X ρ hρ) (@rdT B C W o o' N X ρ i j b Y rd) := by
  refine ⟨fun s g P d => ?_, fun k Q ψ h1 h2 s g P d => ?_, fun Q M h1 s g P d h2 a => ?_⟩
  · rewrite [se_theta o' ρ i j b]
    exact (by with_unfolding_all exact ((h.1 _ _ _ (se_datum' o' d)) :))
  · rewrite [se_gens o' ρ i j b]
    exact (by with_unfolding_all exact ((h.2.1 k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (h1 :))) ((by with_unfolding_all exact (h2 :))) _ _ _ (se_datum' o' d)) :))
  · rewrite [se_xi o' ρ i j b Y]
    exact (by with_unfolding_all exact ((h.2.2 ((by with_unfolding_all exact (Q :))) M ((by with_unfolding_all exact (h1 :))) _ _ _ (se_datum' o' d) ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact (a :)))) :))

theorem ratT' (h : SeriesTie.Rat (@seGood B C W o o' N X ρ hρ) (@rdT B C W o o' N X ρ i j b Y rd)) : SeriesTie.Rat hρ rd := (by with_unfolding_all exact ((ratT (o := o') o h) :))

def cellT (t : CellTie hρ Y rd) : CellTie (@seGood B C W o o' N X ρ hρ) _ (@rdT B C W o o' N X ρ i j b Y rd) where
  supp := (by with_unfolding_all exact (t.supp :))
  cls := (by with_unfolding_all exact (t.cls :))
  coef := (by with_unfolding_all exact (t.coef :))
  rdV := (by with_unfolding_all exact (t.rdV :))
  U_eq := (by with_unfolding_all exact (t.U_eq :))
  psiU_eq := (by with_unfolding_all exact (t.psiU_eq :))
  dat := fun d => (by with_unfolding_all exact ((se_datum o' (t.dat ((by with_unfolding_all exact (d :))))) :))
  dat_onto := fun s g P d => by
    rewrite [se_theta o' ρ i j b]
    exact (by with_unfolding_all exact ((t.dat_onto _ _ _ (se_datum' o' d)) :))
  lev_iff := (by with_unfolding_all exact (t.lev_iff :))
  th_eq := by
    rewrite [se_theta o' ρ i j b]
    exact (by with_unfolding_all exact (t.th_eq :))
  thPsi_iff := by
    rewrite [se_gens o' ρ i j b]
    exact (by with_unfolding_all exact (t.thPsi_iff :))
  thU_eq := by
    rewrite [se_xi o' ρ i j b Y]
    exact (by with_unfolding_all exact (t.thU_eq :))
  thU_off := by
    rewrite [se_xi o' ρ i j b Y]
    exact (by with_unfolding_all exact (t.thU_off :))
  rdV_inj := (by with_unfolding_all exact (t.rdV_inj :))
  mtLat_iff := (by with_unfolding_all exact (t.mtLat_iff :))
  thP_eq := by
    rewrite [se_sum o' ρ i j b]
    exact (by with_unfolding_all exact (t.thP_eq :))

end Setup

end GlobalTheory.HeightCounting.SerCopy

end

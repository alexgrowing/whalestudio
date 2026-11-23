import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ValTransOfEq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

theorem finTypRep_trans_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S S' : Set (Formalism.L2.NG.FinTyp E n)}
    (e : S = S') {α : Type} (f : α ≃ Formalism.L2.Col.FinTypCls S) (x : α) :
    Formalism.L2.Col.finTypRep S (f x) = Formalism.L2.Col.finTypRep S' (f.trans (Equiv.cast (congrArg Formalism.L2.Col.FinTypCls e)) x) := by
  subst e
  rfl

local instance instCMHostTr (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m}

section Two

variable {R : RealDat a.D A.A Ks} {F : Face a.D A.A} {X0 : BaseLevelRowSide a.D} (Y : Read (A3 := A) R F X0)

abbrev occA : Set (Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r) :=
  principalLevelFrame.OccRows R.θ Y.PY (R.MY 0) (fun l => levS _ (R.βY 0) (R.dat0 (R.levR F l)))
    (fun l => levChi _ (R.βY 0) (R.dat0 (R.levR F l))) fun _ => R.e0

def occB : Set (Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r) :=
  {π | ∃ l, isotLB c.to a R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F l))) (levChi _ (R.βY 0) (R.dat0 (R.levR F l))) R.e0
    (principalLevelFrame.FinTyp.conjT π) ≠ ⊥}

theorem occ_eq : occA Y = occB c Y :=
  (by with_unfolding_all exact ((congrArg (fun m : type_of% (@principalLevelFrame.isotL a.D) => {π : Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r | ∃ l,
    m R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F l))) (levChi _ (R.βY 0) (R.dat0 (R.levR F l))) R.e0
      (principalLevelFrame.FinTyp.conjT π) ≠ ⊥}) (isotL_eq c.to a)) :))

def eFTB : a.D.what₂.FT ≃ Formalism.L2.Col.FinTypCls (occB c Y) :=
  Equiv.trans (β := Formalism.L2.Col.FinTypCls (occA Y)) Y.eFT (Equiv.cast (congrArg Formalism.L2.Col.FinTypCls (occ_eq c Y)))

theorem rep_eq (π : a.D.what₂.FT) : principalLevelFrame.rowRepR R.θ (Y.eFT π) = Formalism.L2.Col.finTypRep (occB c Y) (eFTB c Y π) :=
  (by with_unfolding_all exact ((finTypRep_trans_cast (occ_eq c Y) Y.eFT π) :))

theorem prtE_tr (π : a.D.what₂.FT) : Y.Ish.prt π = (isotLB c.to a R.θ Y.PY (R.MY 0)
    (levS _ (R.βY 0) (R.dat0 (R.levR F true))) (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) R.e0
    (principalLevelFrame.FinTyp.conjT (Formalism.L2.Col.finTypRep (occB c Y) (eFTB c Y π)))).map
      (PiTensorProduct.lift : MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap :=
  (Y.prtE π).trans ((by with_unfolding_all exact ((congrArg₂ (fun (m : type_of% (@principalLevelFrame.isotL a.D)) (ρ : Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r) =>
    (m R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true))) (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) R.e0
      (principalLevelFrame.FinTyp.conjT ρ)).map (PiTensorProduct.lift : MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap) (isotL_eq c.to a) (rep_eq c Y π)) :)))

theorem replacementValues_baseLevelTypeParts_eq (π : a.D.what₂.FT) : Y.Iz.prt π = (isotLB c.to a R.θ Y.PY (R.MY 0)
    (levS _ (R.βY 0) (R.dat0 (R.levR F false))) (levChi _ (R.βY 0) (R.dat0 (R.levR F false))) R.e0
    (principalLevelFrame.FinTyp.conjT (Formalism.L2.Col.finTypRep (occB c Y) (eFTB c Y π)))).map
      (PiTensorProduct.lift : MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap :=
  (Y.prtE0 π).trans ((by with_unfolding_all exact ((congrArg₂ (fun (m : type_of% (@principalLevelFrame.isotL a.D)) (ρ : Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r) =>
    (m R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F false))) (levChi _ (R.βY 0) (R.dat0 (R.levR F false))) R.e0
      (principalLevelFrame.FinTyp.conjT ρ)).map (PiTensorProduct.lift : MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap) (isotL_eq c.to a) (rep_eq c Y π)) :)))

theorem prtWE_tr (i : Fin a.D.R.m) (π : a.D.what₂.FT) : Y.IL.prtW i π = (isotLB c.to a R.θ (Y.PW i) (R.MW i (sg0 a.D A.A))
    (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 a.D A.A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 a.D A.A))))
    (R.eWf i (sg0 a.D A.A)) (Formalism.L2.Col.finTypRep (occB c Y) (eFTB c Y π))).map
      (PiTensorProduct.lift : MMap (R.MW i (sg0 a.D A.A)) ≃ₗ[ℂ] _).toLinearMap :=
  (Y.prtWE i π).trans ((by with_unfolding_all exact ((congrArg₂ (fun (m : type_of% (@principalLevelFrame.isotL a.D)) (ρ : Formalism.L2.NG.FinTyp a.D.host.E a.D.R.r) =>
    (m R.θ (Y.PW i) (R.MW i (sg0 a.D A.A))
      (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 a.D A.A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 a.D A.A))))
      (R.eWf i (sg0 a.D A.A)) ρ).map (PiTensorProduct.lift : MMap (R.MW i (sg0 a.D A.A)) ≃ₗ[ℂ] _).toLinearMap)
    (isotL_eq c.to a) (rep_eq c Y π)) :)))

theorem isomFin_tr (i : Fin a.D.R.m) : @principalLevelFrame.IsIsomFin c.to.D (Yc c.to.D 0) (Wc c.to.D ((i))) ((Y.ιW i)) := by
  constructor
  case bij => exact (by with_unfolding_all exact ((Y.isomFin i).bij :))
  case conj => exact (by with_unfolding_all exact ((Y.isomFin i).conj :))
  case lat => exact (by with_unfolding_all exact ((Y.isomFin i).lat :))

set_option maxHeartbeats 800000 in

def read : @Read c.to.D G _ _ Pl0 I0 T (famInThreeCoefficientChange c.to A) Ks _ _ (alg c.to iK) ((by with_unfolding_all exact ((real c.to R) :))) ((by with_unfolding_all exact ((face c.to F) :))) (baseLevelRowSideTransport c X0) :=
  @Read.mk c.to.D G _ _ Pl0 I0 T (famInThreeCoefficientChange c.to A) Ks _ _ (alg c.to iK) ((by with_unfolding_all exact ((real c.to R) :))) ((by with_unfolding_all exact ((face c.to F) :))) (baseLevelRowSideTransport c X0)
    (tup := (by with_unfolding_all exact (Y.tup :)))
    (tupT := (by with_unfolding_all exact (Y.tupT :)))
    (tupT_tup := (by with_unfolding_all exact (Y.tupT_tup :)))
    (tupTie := (by with_unfolding_all exact (Y.tupTie :)))
    (tup0 := (by with_unfolding_all exact (Y.tup0 :)))
    (muAt := (by with_unfolding_all exact (Y.muAt :)))
    (hm := (by with_unfolding_all exact (Y.hm :)))
    (hTop := (by with_unfolding_all exact ((topMult_tr c.to Y.hTop) :)))
    (hinj := (by with_unfolding_all exact ((inj_tr c.to Y.hinj) :)))
    (Ish := (by with_unfolding_all exact ((rowIds c Y.Ish) :)))
    (Iz := (by with_unfolding_all exact ((rowIds c Y.Iz) :)))
    (IL := (by with_unfolding_all exact ((liftIds c Y.IL) :)))
    (Kc := colReal c Y.Kc)
    (PY := (by with_unfolding_all exact ((rowPsi c.to Y.PY) :)))
    (PW := (by with_unfolding_all exact ((fun i => rowPsi c.to (Y.PW i)) :)))
    (eFT := (by with_unfolding_all exact ((eFTB c Y) :)))
    (ιW := (by with_unfolding_all exact (Y.ιW :)))
    (tied := (by with_unfolding_all exact ((recTied_tr c Y.tied) :)))
    (prtE := (by with_unfolding_all exact ((prtE_tr c Y) :)))
    (prtE0 := (by with_unfolding_all exact ((replacementValues_baseLevelTypeParts_eq c Y) :)))
    (prtWE := kc% (prtWE_tr c Y))
    (xi := (by with_unfolding_all exact (Y.xi :)))
    (isomFin := (by with_unfolding_all exact ((isomFin_tr c Y) :)))
    (frameMatch := (by with_unfolding_all exact (Y.frameMatch :)))
    (hF := (by with_unfolding_all exact (Y.hF :)))
    (stdPsi := (by with_unfolding_all exact (Y.stdPsi :)))
    (jA := (by with_unfolding_all exact (Y.jA :)))
    (jA0 := (by with_unfolding_all exact (Y.jA0 :)))
    (eMt := (by with_unfolding_all exact (Y.eMt :)))
    (formsA := (by with_unfolding_all exact (Y.formsA :)))
    (latA := (by with_unfolding_all exact (Y.latA :)))
    (formsAtBottomLevel := (by with_unfolding_all exact (Y.formsAtBottomLevel :)))
    (latA0 := (by with_unfolding_all exact (Y.latA0 :)))
    (formsL := (by with_unfolding_all exact (Y.formsL :)))
    (latL := (by with_unfolding_all exact (Y.latL :)))
    (topRead := (by with_unfolding_all exact ((fun t h x => (val_trans_ofEq (j := Y.Ish.jX (Y.tup t) h)
      (congrFun (congrFun (spCCXP_eq c F Y.tupT Y.hm Y.hTop) true) (Y.tup t)) _).trans (Y.topRead t h x)) :)))
    (topRead0 := (by with_unfolding_all exact ((fun t h x => (val_trans_ofEq (j := Y.Iz.jX (Y.tup t) h)
      (congrFun (congrFun (spCCXP_eq c F Y.tupT Y.hm Y.hTop) false) (Y.tup t)) _).trans (Y.topRead0 t h x)) :)))
    (mtRead := (by with_unfolding_all exact (Y.mtRead :)))
    (mj := (by with_unfolding_all exact ((mjTie c Y.mj) :)))
    (mjRead := (by with_unfolding_all exact ((fun i y => (val_trans_ofEq (j := Y.IL.jMj i) (congrFun (spWc_eq c F Y.tupT Y.hm Y.hTop Y.hinj) i) y).trans
      (Y.mjRead i y)) :)))
    (stable := (by with_unfolding_all exact (Y.stable :)))
    (stable0 := (by with_unfolding_all exact (Y.stable0 :)))
    (eE := (by with_unfolding_all exact (Y.eE :)))
    (eE_read := (by with_unfolding_all exact ((fun x => (val_trans_ofEq (j := Y.Ish.jE) (congrFun (spEEc_eq c F Y.tupT Y.hm Y.hTop) true) x).trans (Y.eE_read x)) :)))
    (dall := (by with_unfolding_all exact ((Y.dall.trans (congrArg (fun m : type_of% (@Mult.Mult a.D) => Module.finrank ℂ
      (m R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true))) (levChi _ (R.βY 0) (R.dat0 (R.levR F true))))) (mult_eq c.to a))) :)))
    (junk := (by with_unfolding_all exact (Y.junk :)))
    (cen0 := fun cG h => (by with_unfolding_all exact ((Y.cen0 _ (keep_back c.to c.same' (cG := (by with_unfolding_all exact (cG :))) ((by with_unfolding_all exact (h :))))) :)))
    (cen1 := fun cG h => (by with_unfolding_all exact ((Y.cen1 _ (keep_back c.to c.same' (cG := (by with_unfolding_all exact (cG :))) ((by with_unfolding_all exact (h :))))) :)))
    (lam := (by with_unfolding_all exact (Y.lam :)))
    (occ := (by with_unfolding_all exact (Y.occ :)))
    (kap := (by with_unfolding_all exact (Y.kap :)))
    (bu := (by with_unfolding_all exact (Y.bu :)))
    (ze := (by with_unfolding_all exact (Y.ze :)))

end Two

section Three

variable {R : RealDat3 a.D A Ks} {F : Face3 a.D A} {X0 : BaseLevelRowSide a.D} {Y : Read (A3 := A) R.toRealDat F.lv2 X0}

variable (R) in

def partsB : Parts R :=
  ((by with_unfolding_all exact ((letI := alg c.to iK; (real3 c.to R).EEp3) :)), (by with_unfolding_all exact ((letI := alg c.to iK; (real c.to R.toRealDat).EEat) :)),
    (by with_unfolding_all exact ((letI := alg c.to iK; (real3 c.to R).Wp3) :)))

variable (Z : ReadL R F X0 Y) (u : Parts R)

def eRRu : (Fin ((cxW R F u).data F.cr true).D → a.D.what₂.LL) ≃ₗ[a.D.what₂.LL] a.D.div.RR.V := (by with_unfolding_all exact (Z.eRR :))

def riemannRochSpaceCoordinateEquiv : (Fin ((cxW R F u).data F.cr false).D → a.D.what₂.LL) ≃ₗ[a.D.what₂.LL] X0.s.RR.V := (by with_unfolding_all exact (Z.eRR0 :))

def jWu (i : Fin a.D.R.m) :
    (Fin (((cxW R F u).data F.cr false).dW i) → a.D.what₂.LL) →ₛₗ[a.D.what₂.embLL] a.D.what₂.Mj ((i : ℕ) + 1) := (by with_unfolding_all exact ((Z.jW i) :))

theorem jEEu : ∀ y, (Y.Ish.jE (a.D.jEE (eRRu Z u y))).1 =
    PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt a.D.what₂.embLL A.A.v0) (E := R.HE.H)
      ((cxW R F u).iC F.cr true A.A.μ0 (Cx.cpt A.A.v0.embedding y)))) := (by with_unfolding_all exact (Z.jEE :))

theorem jEE0u : ∀ y, (Y.Iz.jE (X0.s.jEE (riemannRochSpaceCoordinateEquiv Z u y))).1 =
    PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt a.D.what₂.embLL A.A.v0) (E := R.HE.H)
      ((cxW R F u).iC F.cr false A.A.μ0 (Cx.cpt A.A.v0.embedding y)))) := (by with_unfolding_all exact (Z.jEE0 :))

theorem metu : ∀ v, v ≠ A.A.v0 → ∀ x y, Formalism.HermitianLatticesTheory.majAt a.D.div.RR.b a.D.div.RR.X v (eRRu Z u x) (eRRu Z u y) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun a.D.what₂.LL _) ((cxW R F u).data F.cr true).XE v x y := (by with_unfolding_all exact (Z.met :))

theorem met0u : ∀ v, v ≠ A.A.v0 → ∀ x y, Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X v (riemannRochSpaceCoordinateEquiv Z u x) (riemannRochSpaceCoordinateEquiv Z u y) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun a.D.what₂.LL _) ((cxW R F u).data F.cr false).XE v x y := (by with_unfolding_all exact (Z.met0 :))

include Z in
open Classical in

theorem etaJu : ∀ (i : Fin a.D.R.m) w, a.D.what₂.etaJ ((i : ℕ) + 1) w =
    if a.D.plEq w ∈ R.twPl then A.A.fam.etaJ F.P0 F.ψ0 (A.fam3.toSub2 (cxW R F u).zs) i (R.mu (a.D.plEq w)) (a.D.plEq w) else 0 :=
  (by with_unfolding_all exact (Z.etaJ :))

def readL : @ReadL c.to.D G _ _ Pl0 I0 T (famInThreeCoefficientChange c.to A) Ks _ _ (alg c.to iK) (real3 c.to R) (face3 c.to F) (baseLevelRowSideTransport c X0)
    ((read c Y)) :=
  @ReadL.mk c.to.D G _ _ Pl0 I0 T (famInThreeCoefficientChange c.to A) Ks _ _ (alg c.to iK) (real3 c.to R) (face3 c.to F) (baseLevelRowSideTransport c X0) ((by with_unfolding_all exact ((read c Y) :)))
    (eRR := (by with_unfolding_all exact ((eRRu Z (partsB c R)) :)))
    (eRR0 := (by with_unfolding_all exact ((riemannRochSpaceCoordinateEquiv Z (partsB c R)) :)))
    (jEE := (by with_unfolding_all exact ((fun y => (val_trans_ofEq (j := Y.Ish.jE) (congrFun (spEEc_eq c F.lv2 Y.tupT Y.hm Y.hTop) true) _).trans
      (jEEu Z (partsB c R) y)) :)))
    (jEE0 := (by with_unfolding_all exact ((fun y => (val_trans_ofEq (j := Y.Iz.jE) (congrFun (spEEc_eq c F.lv2 Y.tupT Y.hm Y.hTop) false) _).trans
      (jEE0u Z (partsB c R) y)) :)))
    (met := (by with_unfolding_all exact ((metu Z (partsB c R)) :)))
    (met0 := (by with_unfolding_all exact ((met0u Z (partsB c R)) :)))
    (rr := kc% Z.rr)
    (rr0 := kc% Z.rr0)
    (jW := (by with_unfolding_all exact ((jWu Z (partsB c R)) :)))
    (jW_read := (by with_unfolding_all exact (Z.jW_read :)))
    (etaJ := (by with_unfolding_all exact ((etaJu Z (partsB c R)) :)))

end Three

end GlobalTheory.Mem.R3.Tr

end

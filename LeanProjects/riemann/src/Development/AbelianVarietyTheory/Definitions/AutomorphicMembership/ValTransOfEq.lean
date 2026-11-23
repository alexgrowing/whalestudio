import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Generic

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {N : Type} [AddCommGroup N] [Module ℂ N] {P P' : Submodule ℂ N}
  {ip : N → N → ℂ} {j : X ≃ₗ[ℂ] P}

theorem hilbTie_ofEq (e : P = P') (h : HilbTie P ip j) : HilbTie P' ip (j.trans (LinearEquiv.ofEq _ _ e)) := fun x y => h x y

theorem projTie_ofEq {Y : Type} {f : Y → X} {g g' : Y → N} (e : P = P') (h : ProjTie P ip j f g) (hg : ∀ y, g' y = g y) :
    ProjTie P' ip (j.trans (LinearEquiv.ofEq _ _ e)) f g' := fun x y => (h x y).trans (congrArg (ip (j x)) (hg y).symm)

omit [NormedAddCommGroup X] [InnerProductSpace ℂ X] in

theorem le_of_eqs {Q Q' : Submodule ℂ N} (e : P = P') (e' : Q = Q') (h : P ≤ Q) : P' ≤ Q' := e ▸ e' ▸ h

theorem val_trans_ofEq (e : P = P') (x : X) : ((j.trans (LinearEquiv.ofEq _ _ e)) x).1 = (j x).1 := rfl

theorem map_incl {Q Q' : Submodule ℂ N} {Z : Type} (e : P = P') (e' : Q = Q') (h : P ≤ Q) (j : X ≃ₗ[ℂ] P) {f : Q → Z} (f' : Q' → Z)
    (hf : ∀ v, f' (LinearEquiv.ofEq _ _ e' v) = f v) (y : X) :
    f' (Submodule.inclusion (le_of_eqs e e' h) ((j.trans (LinearEquiv.ofEq _ _ e)) y)) = f (Submodule.inclusion h (j y)) := by
  subst e e'
  exact hf (Submodule.inclusion h (j y))

end Generic

section Chain

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A} {tupT : a.D.what₂.Tup → T}
  {hm : 0 < a.D.R.m} {hTop : TopMultH R}

def stepB (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : spCC c F tupT hm hTop l μ (k + 1)) : (toChainReal R F tupT hm hTop).Amb k :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioC l ((μ)) k ((v))).1 : _))

theorem stepB_eq (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) :
    stepB c l μ k (LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v) =
      ((toChainReal R F tupT hm hTop).ioC l μ k v).1 := (ioCB_eq c l μ k v)

def topB (l : Bool) (μ : a.D.what₂.Tup) (v : spCCX c F tupT hm hTop l μ) : (toChainReal R F tupT hm hTop).Amb (a.D.R.m - 1) :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioX l ((μ)) ((v))).1 : _))

theorem topB_eq (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) :
    topB c l μ (LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v) =
      ((toChainReal R F tupT hm hTop).ioX l μ v).1 := (ioXB'_eq c l μ v)

section Rows

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {X : RowSide a.D EE} {l : Bool}

def rowIds (I : RowIds X (toChainReal R F tupT hm hTop) l) : RowIds (rowSide c X) (chainB c.to F tupT hm hTop) l :=
  @RowIds.mk c.to.D EE _ _ _ (rowSide c X) (chainB c.to F tupT hm hTop) l
    ((by with_unfolding_all exact ((I.jE.trans (LinearEquiv.ofEq _ _ (congrFun (spEEc_eq c F tupT hm hTop) l))) :)))
    ((by with_unfolding_all exact ((fun (μ : a.D.what₂.Tup) (h : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) => (I.jM μ h j h1 h2).trans
      (LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j))) :)))
    ((by with_unfolding_all exact ((fun (μ : a.D.what₂.Tup) (h : Used0 a.D μ) => (I.jX μ h).trans
      (LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ))) :)))
    ((I.prt))

set_option maxHeartbeats 800000 in

theorem rowSideReal_tr {I : RowIds X (toChainReal R F tupT hm hTop) l} {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE}
    {ty : Fin n → a.D.what₂.FT} (H : RowSideReal X (toChainReal R F tupT hm hTop) l I bs ty) :
    RowSideReal (rowSide c X) (chainB c.to F tupT hm hTop) l (rowIds c I) bs ((ty)) := by
  refine @RowSideReal.mk _ _ _ _ _ _ _ _ _ _ _ _ ?parY ?lvl ?lvlP ?lvlX ?ee ?mult ?multX ?io0 ?io0X ?io ?ioTop ?ft ?prt_disj
  case parY =>
    exact (H.parY)
  case lvl =>
    kexactB (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) => le_of_eqs (congrFun (spEEc_eq c F tupT hm hTop) l) (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) 0) (H.lvl μ hμ))
  case lvlP =>
    kexactB (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) =>
      le_of_eqs (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) j) (H.lvlP μ hμ j h1 h2))
  case lvlX =>
    kexactB (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) => le_of_eqs (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) (H.lvlX μ hμ))
  case ee =>
    kexactB (hilbTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) H.ee)
  case mult =>
    kexactB (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ a.D.R.m - 1) =>
      hilbTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (H.mult μ hμ j h1 h2))
  case multX =>
    kexactB (fun (h : 1 ≤ a.D.R.m) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) =>
      hilbTie_ofEq (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (H.multX h μ hμ))
  case io0 =>
    kexactB (fun (h : 2 ≤ a.D.R.m) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) (H.io0 h μ hμ (okB_imp c ok)) fun y =>
        map_incl (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (0 + 1))
          (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (0 + 1)) (H.lvlP μ hμ 1 le_rfl (by omega))
          (I.jM μ hμ 1 le_rfl (by omega)) (stepB c l μ 0) (stepB_eq c l μ 0) y)
  case io0X =>
    kexactB (fun (h : a.D.R.m = 1) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (spEEc_eq c F tupT hm hTop) l) (H.io0X h μ hμ (okB_imp c ok)) fun y =>
        congrArg (cast (congrArg (toChainReal R F tupT hm hTop).Amb (show a.D.R.m - 1 = 0 by omega)))
          (map_incl (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ)
            (H.lvlX μ hμ) (I.jX μ hμ) (topB c l μ) (topB_eq c l μ) (cast (congrArg (X.Mult μ) h.symm) y)))
  case io =>
    kexactB (fun (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) (j : ℕ) (h1 : 1 ≤ j)
        (h2 : j + 1 ≤ a.D.R.m - 1) =>
      projTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) j) (H.io μ hμ (okB_imp c ok) j h1 h2) fun y =>
        map_incl (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (j + 1))
          (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (j + 1)) (H.lvlP μ hμ (j + 1) (by omega) h2)
          (I.jM μ hμ (j + 1) (by omega) h2) (stepB c l μ j) (stepB_eq c l μ j) y)
  case ioTop =>
    kexactB (fun (h : 2 ≤ a.D.R.m) (μ : a.D.what₂.Tup) (hμ : Used0 a.D μ) (ok : okB c F tupT hm hTop l μ) =>
      projTie_ofEq (congrFun (congrFun (congrFun (spCCP_eq c F tupT hm hTop) l) μ) (a.D.R.m - 1)) (H.ioTop h μ hμ (okB_imp c ok)) fun y =>
        map_incl (congrFun (congrFun (spCCXP_eq c F tupT hm hTop) l) μ) (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ)
          (H.lvlX μ hμ) (I.jX μ hμ) (topB c l μ) (topB_eq c l μ) y)
  case ft =>
    kexactB (fun σ => cast (congrArg (· ∈ I.prt (ty σ)) (val_trans_ofEq (j := I.jE) (congrFun (spEEc_eq c F tupT hm hTop) l) (bs σ)).symm) (H.ft σ))
  case prt_disj =>
    exact (H.prt_disj)

end Rows

variable {hinj : ∀ i t, Function.Injective (R.extV i t)}

variable (F tupT hm hTop hinj) in

def spWc : type_of% (toLiftReal R F tupT hm hTop hinj).Wc := ((liftB c.to F tupT hm hTop hinj).Wc)

variable (F tupT hm hTop hinj) in

theorem spWc_eq : (toLiftReal R F tupT hm hTop hinj).Wc = spWc c F tupT hm hTop hinj := (lift_Wc c.to F tupT hm hTop hinj)

variable (F tupT hm hTop hinj) in

def spMultW : type_of% (toLiftReal R F tupT hm hTop hinj).MultW := ((liftB c.to F tupT hm hTop hinj).MultW)

variable (F tupT hm hTop hinj) in

theorem spMultW_eq : (toLiftReal R F tupT hm hTop hinj).MultW = spMultW c F tupT hm hTop hinj := (lift_MultW c.to F tupT hm hTop hinj)

def liftIds (I : LiftIds (toLiftReal R F tupT hm hTop hinj)) : LiftIds (liftB c.to F tupT hm hTop hinj) :=
  @LiftIds.mk c.to.D (chainB c.to F tupT hm hTop) (liftB c.to F tupT hm hTop hinj)
    ((by with_unfolding_all exact ((fun i : Fin a.D.R.m => (I.jMj i).trans (LinearEquiv.ofEq _ _ (congrFun (spWc_eq c F tupT hm hTop hinj) i))) :)))
    ((I.jMt)) ((I.prtW))

theorem liftTie_tr {I : LiftIds (toLiftReal R F tupT hm hTop hinj)} (H : LiftTie (toLiftReal R F tupT hm hTop hinj) I) :
    LiftTie (liftB c.to F tupT hm hTop hinj) (liftIds c I) := by
  refine @LiftTie.mk _ _ _ _ ((H.hol)) (kc% (fun i => hilbTie_ofEq (congrFun (spWc_eq c F tupT hm hTop hinj) i) (H.mj i))) ((H.mt)) ?_ (kc% H.isot) ((H.prtW_disj)) ((H.lamP))
  kexactB (cast (congrArg₂ (fun (P : type_of% (toLiftReal R F tupT hm hTop hinj).MultW) (Q : type_of% (toLiftReal R F tupT hm hTop hinj).Wc) =>
    ∀ μ (hμ : Used0 a.D μ) (i : Fin a.D.R.m) (x : a.D.what₂.Mt μ (i + 1)) (w : (toLiftReal R F tupT hm hTop hinj).AmbW i),
      Lift.IsThetaP ((toLiftReal R F tupT hm hTop hinj).measV μ i) ((toLiftReal R F tupT hm hTop hinj).fdV μ i)
        ((toLiftReal R F tupT hm hTop hinj).thW μ i) ((toLiftReal R F tupT hm hTop hinj).ptW μ i) ((toLiftReal R F tupT hm hTop hinj).ioK i)
        ((toLiftReal R F tupT hm hTop hinj).Amt μ i) ((toLiftReal R F tupT hm hTop hinj).thC μ i) → w ∈ P i →
      w ∘ₗ (toLiftReal R F tupT hm hTop hinj).embK i = (toLiftReal R F tupT hm hTop hinj).thC μ i (I.jMt μ hμ i x) →
      (toLiftReal R F tupT hm hTop hinj).eW i ∘ₗ w ∈ Q i →
      (I.jMj i (a.D.what₂.thetaP μ (i + 1) x)).1 = (toLiftReal R F tupT hm hTop hinj).eW i ∘ₗ w)
    (spMultW_eq c F tupT hm hTop hinj) (spWc_eq c F tupT hm hTop hinj)) (kc% H.theta))

theorem recTied_tr {X0 : BaseLevelRowSide a.D} {Ish : RowIds (RowSide.sharp a.D) (toChainReal R F tupT hm hTop) true}
    {Iz : RowIds X0.s (toChainReal R F tupT hm hTop) false} {IL : LiftIds (toLiftReal R F tupT hm hTop hinj)} {K : ColReal a.D}
    (H : RecTied a.D X0 (toChainReal R F tupT hm hTop) Ish Iz (toLiftReal R F tupT hm hTop hinj) IL K) :
    RecTied c.to.D (baseLevelRowSideTransport c X0) (chainB c.to F tupT hm hTop) ((rowIds c Ish)) ((by with_unfolding_all exact @rowIds B C a c G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R F tupT hm hTop (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X0) false Iz)) (liftB c.to F tupT hm hTop hinj)
      (liftIds c IL) (colReal c K) :=
  @RecTied.mk _ _ _ _ _ _ _ _ ((rowSideReal_tr c H.sharp)) ((by with_unfolding_all exact @rowSideReal_tr B C a c G ‹Group G› ‹Fintype G› Pl0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R F tupT hm hTop (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X0) false Iz (@Rows.Data.D0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.onb0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.ft0 (@Late.D B C a).R (@Late.D B C a).what₂) (@RecTied.base (@Late.D B C a) X0 (@toChainReal (@Late.D B C a) G ‹Group G› ‹Fintype G› Pl0 T A Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK R F tupT hm hTop) Ish Iz (@toLiftReal (@Late.D B C a) G ‹Group G› ‹Fintype G› Pl0 T A Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK R F tupT hm hTop hinj) IL K H))) (liftTie_tr c H.lift)
    (@ColTieR.mk _ _ _ ((H.col.tup)) ((H.col.xi0)) ((H.col.bu)))

def mjTie (x : MjTie R F) : @MjTie c.to.D G _ _ Pl0 T (famM c.to A) Ks _ _ (alg c.to iK) (real c.to R) (face c.to F) :=
  @MjTie.mk c.to.D G _ _ Pl0 T (famM c.to A) Ks _ _ (alg c.to iK) (real c.to R) (face c.to F) ((x.eW))
    ((by with_unfolding_all exact ((cast (congrArg (fun W : type_of% R.Wat => ∀ i, LinearMap.range (x.eW i) =
      (W i (sg0 a.D A) (R.levL F false (sg0 a.D A))).comap (R.HW i (sg0 a.D A)).e) (wat_eq c.to R)) x.eW_range) :)))
    ((x.eW_norm)) ((x.eW_lat))

end Chain

end GlobalTheory.Mem.R3.Tr

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne

noncomputable section

namespace GlobalTheory.Core.Cls

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure TruePt (K : Ctx) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)) : Type 1 where

  isOver : K.Over B.toPre
  good : ∃ C5 c6 Cb : ℝ, K.Good C5 c6 Cb

  sc : O.L.sc = K.s
  wt : WtEq O.L K.a K.b
  val : Val K.C K.cD K.ch O.L
  canon : CanonInst O.Gx
  K_eq : O.K = K.C.GK
  cX_eq : O.cX = K.C.cX

  pin : ColPin w

  S : SelB O.ex
  std : TC.StdC w.I w.l Z S.cols
  stdLv : ∀ u, TC.StdLvC w.I w.l Z u (S.cols.forms u)
  stdDt : TC.StdDt w.I w.l Z S.full.1.base.dt
  cf_eq : S.cf = TC.cf w.I w.l Z
  xi_eq : S.tp.xi = w.I.xi
  tw_eq : O.ex.tw = w.tw Z
  lev_eq : O.ex.lev = S.full.1.base.lev0
  errX_eq : O.ex.errX = Formalism.L2.Herm.toErrXS S.full.1
  piG_eq : O.ex.errX.piG = w.px.piG
  piT_eq : O.ex.errX.piT = w.px.piT
  qp : TC.QpIs w.I O.X.Qp
  isRec : IsRecG K.s (w.D Z) O.gatT O.ex.cmp S.g.herm S.g.forms
  gpl : Formalism.L2.Herm.SymmetricGroupCompatibleAtPlaces (w.D Z) S.full.1.base.toHermColsCh S.full.1.g O.gatT
  stdKer : TC.StdKer w.I w.l Z S.ker
  stdRd : GlobalTheory.Pdv.StdRd w.I w.l Z S.ker
  entC : GlobalTheory.Pdv.IsEntC S.ker
  dsig : ∀ τ, (w.D Z).dsig τ = Vol.trueDsig B.R (B.hc τ)

abbrev TP : Type 1 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), TruePt K w Z O → Prop

def IsTrueWith (P : TP) (D : D7) (O : Obj D) : Prop :=
  ∃ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O' : Obj (w.D Z)) (p : TruePt K w Z O'),
    P K B f T w Z O' p ∧ (⟨D, O⟩ : Σ D : D7, Obj D) = ⟨w.D Z, O'⟩

def IsTrue (D : D7) (O : Obj D) : Prop := IsTrueWith (fun _ _ _ _ _ _ _ _ => True) D O

theorem IsTrueWith.ind {P : TP} {R : ∀ D : D7, Obj D → Prop}
    (h : ∀ K B f T (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)) (p : TruePt K w Z O), P K B f T w Z O p → R (w.D Z) O)
    {D : D7} {O : Obj D} (hD : IsTrueWith P D O) : R D O := by
  obtain ⟨K, B, f, T, w, Z, O', p, hp, e⟩ := hD
  cases e
  exact h K B f T w Z _ p hp

theorem IsTrue.ind {R : ∀ D : D7, Obj D → Prop}
    (h : ∀ K B f T (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), TruePt K w Z O → R (w.D Z) O)
    {D : D7} {O : Obj D} (hD : IsTrue D O) : R D O :=
  IsTrueWith.ind (fun K B f T w Z O p _ => h K B f T w Z O p) hD

theorem IsTrue.selB {D : D7} {O : Obj D} (h : IsTrue D O) : Nonempty (SelB O.ex) :=
  IsTrue.ind (R := fun _ O => Nonempty (SelB O.ex)) (fun _ _ _ _ _ _ _ p => ⟨p.S⟩) h

abbrev objF {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : Obj (Fm.D x i) :=
  ⟨Fm.L x i, Fm.gatT x i, Fm.Gx x i, Fm.Gy x i, Fm.GK, Fm.X x i, Fm.cX, Fm.ex x hx i⟩

def TrueF {eps : ℝ} (Fm : FamP eps) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), IsTrue (Fm.D x i) (objF Fm x hx i)

theorem TrueF.selBF {eps : ℝ} {Fm : FamP eps} (h : TrueF Fm) : SelBF Fm := ⟨0, fun x _ hx i => (h x hx i).selB⟩

end GlobalTheory.Core.Cls

end

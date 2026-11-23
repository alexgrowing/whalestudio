import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

noncomputable section

namespace GlobalTheory.Svd

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2

def ModelsAt (D : D7) (O : Obj D) : Prop :=
  G.LatTied O.gatT O.Gx O.Gy → 2 * G.rG O.L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D O.Gy O.ex.cmp O.X O.ex.tw

structure StdAt {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l))
    (O : Obj (I.rec7 l Z)) (t : KerEntTied O.ex) : Prop where
  ok : I.Ok
  pins : TC.Pins B X
  isTw : I.IsTw
  jets : ColIn.JetsIn I
  tw : O.ex.tw = I.tw l l0 Z
  ker : I.StdKer l Z t
  entC : GlobalTheory.Pdv.IsEntC t
  adapted : t.Adapted
  top : t.TopPinned

def StdTie (D : D7) (O : Obj D) (t : KerEntTied O.ex) : Prop :=
  ∃ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l))
    (O' : Obj (I.rec7 l Z)) (t' : KerEntTied O'.ex), StdAt I l l0 Z O' t' ∧
    (⟨D, O, t⟩ : Σ (D : D7) (O : Obj D), KerEntTied O.ex) = ⟨I.rec7 l Z, O', t'⟩

theorem StdTie.intro {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {l0 : I.Law0 l} {Z : TC.Later B (I.cols l)}
    {O : Obj (I.rec7 l Z)} {t : KerEntTied O.ex} (h : StdAt I l l0 Z O t) : StdTie (I.rec7 l Z) O t :=
  ⟨B, X, I, l, l0, Z, O, t, h, rfl⟩

theorem StdTie.ind {R : ∀ (D : D7) (O : Obj D), KerEntTied O.ex → Prop}
    (h : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l))
      (O : Obj (I.rec7 l Z)) (t : KerEntTied O.ex), StdAt I l l0 Z O t → R (I.rec7 l Z) O t)
    {D : D7} {O : Obj D} {t : KerEntTied O.ex} (hD : StdTie D O t) : R D O t := by
  obtain ⟨B, X, I, l, l0, Z, O', t', hs, e⟩ := hD
  cases e
  exact h B X I l l0 Z _ _ hs

def ServH {Bd : GlobalTheory.Fc.BdT} (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex) (𝒜 : FamClass) (σ : GlobalTheory.Fc.RawSel Bd 𝒜) : Prop :=
  (Closed 𝒜 fun Fm _ => GlobalTheory.TwU.RowTwU Fm) ∧ GlobalTheory.Fc.AtAll (fun D O c b => GlobalTheory.Pdv.At O.ex (ker D O c b).ent) 𝒜 σ

section Part

open GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

variable {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B}

structure Part (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) : Type 1 where
  pin : ColPin w
  col : ColT w Z
  errX : O.errX = Formalism.L2.Herm.toErrXS col.full.1
  tp : Formalism.L2.Host.TupTied (w.D Z) (TC.cf w.I w.l Z) O.nch
  xi : tp.xi = w.I.xi
  qp : TC.QpIs w.I O.X.Qp
  ker0 : KerFam (w.D Z) col.Gt col.cmp (w.tw Z) O.Gy
  ker_eq : (⟨O.gatT, O.cmp, O.tw, O.ker⟩ : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)),
    KerFam (w.D Z) Gt cmp tw O.Gy) = ⟨col.Gt, col.cmp, w.tw Z, ker0⟩
  ker : KerT col O.X O.Gy ker0

def HasPart : CP := fun _ _ _ _ w Z c => Nonempty (Part w Z c.O)

def HasPartAnd (P : ZP) : CP := fun K B f T w Z c => HasPart K B f T w Z c ∧ P K B f T w Z

end Part

end GlobalTheory.Svd

end

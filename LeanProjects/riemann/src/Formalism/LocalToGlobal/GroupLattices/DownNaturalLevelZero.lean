import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Forms0 (D : D7) (u : D.what₂.Word) where
  atT : AtTTied u

  cls0 : ClsTied u 0 (Nat.zero_le _)

  val0 : ValTied u atT.eV 0 (Nat.zero_le _) cls0

  gl : GLoc D.host.F D.host.E (sigD D) D.host.g
  gl_K : ∀ i, (gl.piG i : D.host.E) ∈ D.host.K

  glev0 : GLev cls0.lev gl D.R.k D.R.t 0 D.R.k (D.R.N 0) false

  lv0 : LvTied u atT 0 (Nat.zero_le _)
  fMe0 : ∀ v, cls0.lev.fM (atT.eV v).1 (atT.eV v).2 ≃+ (D.mem u).A.Fv v
  fv0 : FvTie lv0 cls0 fMe0
  up_natural_level_zero : UpNatTie lv0 cls0 val0
  down_natural_level_zero : DnNatTie lv0 cls0 val0
  norm0 : NormTie val0
  bw0 : BwTie atT val0

namespace Forms0

variable {D : D7} {u : D.what₂.Word} (T : Forms0 D u)

def cls : ∀ (i : ℕ) (hi : i ≤ D.R.m), i = 0 → ClsTied u i hi
  | 0, _, _ => T.cls0

def val : ∀ (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0), ValTied u T.atT.eV i hi (T.cls i hi h)
  | 0, _, _ => T.val0

def lv : ∀ (i : ℕ) (hi : i ≤ D.R.m), i = 0 → LvTied u T.atT i hi
  | 0, _, _ => T.lv0

def fMe : ∀ (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0) v, (T.cls i hi h).lev.fM (T.atT.eV v).1 (T.atT.eV v).2 ≃+ (D.mem u).A.Fv v
  | 0, _, _ => T.fMe0

theorem fv : ∀ (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0), FvTie (T.lv i hi h) (T.cls i hi h) (T.fMe i hi h)
  | 0, _, _ => T.fv0

theorem upN : ∀ (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0), UpNatTie (T.lv i hi h) (T.cls i hi h) (T.val i hi h)
  | 0, _, _ => T.up_natural_level_zero

theorem dnN : ∀ (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0), DnNatTie (T.lv i hi h) (T.cls i hi h) (T.val i hi h)
  | 0, _, _ => T.down_natural_level_zero

theorem norm : ∀ (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0), NormTie (T.val i hi h)
  | 0, _, _ => T.norm0

theorem bw : ∀ (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0), BwTie T.atT (T.val i hi h)
  | 0, _, _ => T.bw0

theorem cls_zero : T.cls 0 (Nat.zero_le _) rfl = T.cls0 := rfl

theorem val_zero : T.val 0 (Nat.zero_le _) rfl = T.val0 := rfl

theorem lv_zero : T.lv 0 (Nat.zero_le _) rfl = T.lv0 := rfl

end Forms0

def FormsTied.to0 {D : D7} {u : D.what₂.Word} (T : FormsTied D u) : Forms0 D u where
  atT := T.atT
  cls0 := T.cls 0 (Nat.zero_le _)
  val0 := T.val 0 (Nat.zero_le _)
  gl := T.gl
  gl_K := T.gl_K
  glev0 := by
    have h := T.glev 0 (Nat.zero_le _)
    have hm := D.R.two_le_m
    have e1 : aOf D.R 0 = D.R.k := by unfold aOf; rw [if_pos (by omega)]; rfl
    have e2 : skipOf D.R 0 = D.R.k := by unfold skipOf; rw [if_pos (by omega)]
    have e3 : fcOf D.R 0 = D.R.N 0 := fcOf_lt (by omega)
    have e4 : decide (0 = D.R.m) = false := decide_eq_false (by omega)
    rw [e1, e2, e3, e4] at h
    exact h
  lv0 := T.lv 0 (Nat.zero_le _)
  fMe0 := T.fMe 0 (Nat.zero_le _)
  fv0 := T.fv 0 (Nat.zero_le _)
  up_natural_level_zero := T.upN 0 (Nat.zero_le _)
  down_natural_level_zero := T.dnN 0 (Nat.zero_le _)
  norm0 := T.norm 0 (Nat.zero_le _)
  bw0 := T.bw 0 (Nat.zero_le _)

def Joint0 {D : D7} (L0 : LevelData D) (u : D.what₂.Word) (T : Forms0 D u) : Prop :=
  SameCar (rank_eq_first_level D.R) (L0 u).Lb T.cls0.lev.Lb (L0 u).Uloc T.cls0.lev.Uloc (L0 u).U T.cls0.lev.U
    (fun c => ((L0 u).y c).1) (fun c => (T.cls0.y c).1)
    (fun c s => ((L0 u).stabI c s).1) (fun c s => (T.cls0.stabI c s).1)

theorem Joint.to0 {D : D7} {X : Formalism.L2.Herm.ColsHerm D} {u : D.what₂.Word} {T : FormsTied D u} (h : Joint X u T) :
    Joint0 X.base.lev0 u T.to0 := h.car0

end Formalism.L2.Forms

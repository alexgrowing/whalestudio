import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RowPk (D : D7) : Type 1 where
  G' : Type
  [grp : Group G']
  [fin : Fintype G']
  Pl0 : Type
  T : Type
  A : FamIn D.what₂.LL G' Pl0 T D.R.m
  Ks : Type
  [fld : Field Ks]
  [nf : NumberField Ks]
  [iK : Algebra Ks D.what₂.LL]
  R : RealDat D A Ks
  F : Face D A
  eE : D.what₂.EE →ₗ[ℂ] R.HE.H

attribute [instance] RowPk.grp RowPk.fin RowPk.fld RowPk.nf RowPk.iK

def RowPk.SAt {D : D7} (p : RowPk D) (F₀ : ∀ u, Forms0 D u) : Type 1 := Top.Bl.SAt p.R p.F p.eE F₀

def upL {B : Base} {C : Cols B} (a : Late B C) (S' : SStage B C a.W) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V)
    (h : B.Word → ℝ) : Late B C := ⟨a.W, (Db.setDivZ a N h).V, S', a.N, a.G⟩

set_option maxHeartbeats 4000000 in

def RowPk.up {B : Base} {C : Cols B} (a : Late B C) (S' : SStage B C a.W) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V)
    (h : B.Word → ℝ) (p : RowPk a.D) : RowPk (upL a S' N h).D :=
  @RowPk.mk (upL a S' N h).D p.G' p.grp p.fin p.Pl0 p.T (famM (upL a S' N h) p.A) p.Ks p.fld p.nf (alg (upL a S' N h) p.iK)
    (real (upL a S' N h) p.R) (face (upL a S' N h) p.F) ((p.eE))

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

set_option maxHeartbeats 4000000 in

def pkOf {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (r : RowsT K w Z Wt p0) : RowPk (Late.D Z) where
  G' := _
  Pl0 := _
  T := _
  Ks := _
  A := _
  R := r.r.z.R.toRealDat
  F := r.r.z.F.lv2
  eE := r.r.Y.eE

set_option maxHeartbeats 4000000 in

theorem sx_eq {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (r : RowsT K w Z Wt p0) (col : ColT w Z) :
    SX K B f T w Z Wt p0 r col = (pkOf r).SAt fun u => (col.C.forms u).to0 := (Eq.refl (SX K B f T w Z Wt p0 r col))

set_option maxHeartbeats 4000000 in

def LevelThreeCondition (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (l : Lv3 𝒮 K w Z) (S' : SStage B w.C Z.W)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ),
    ∃ l' : Lv3 𝒮 K w (upL Z S' N h), pkOf l'.what₂ = (pkOf l.what₂).up Z S' N h

set_option maxHeartbeats 4000000 in

def SxMv : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
    (r : RowsT K w Z Wt p0) (col : ColT w Z) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (p0' : BaseLevelRowSide (w.D (Db.setDivZ Z N h))) (t : RowsT K w (Db.setDivZ Z N h) Wt p0') (col' : ColT w (Db.setDivZ Z N h)),
    HEq (pkOf t) ((pkOf r).up Z Z.S N h) → Nonempty (SX K B f T w Z Wt p0 r col) →
      Nonempty (SX K B f T w (Db.setDivZ Z N h) Wt p0' t col')

set_option maxHeartbeats 4000000 in

def SameCar {D : D7} (F F' : ∀ u, Forms0 D u) : Prop :=
  ∀ u : D.what₂.Word, (F' u).cls0.lev.Lb = (F u).cls0.lev.Lb ∧ (F' u).cls0.lev.U = (F u).cls0.lev.U ∧
    HEq (F' u).cls0.lev.chi (F u).cls0.lev.chi ∧ (F' u).cls0.y = (F u).cls0.y ∧ (F' u).val0.eY = (F u).val0.eY

theorem SameCar.refl {D : D7} (F : ∀ u, Forms0 D u) : SameCar F F := fun _ => ⟨rfl, rfl, HEq.rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in

def SameStd : Prop :=
  ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Zn : New (Late.D Z)) (col : ColT w Z)
    (col' : ColT w (reL Z Zn)) (F₁ : ∀ u, Forms0 (reL Z Zn).D u), SameL Z Zn (fun u => (col.C.forms u).to0) F₁ →
      SameCar F₁ fun u => (col'.C.forms u).to0

end GlobalTheory.Mem.SRe

end

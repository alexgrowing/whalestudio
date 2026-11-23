import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.See

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PiLocalization₂

variable {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D)

set_option maxHeartbeats 4000000 in

def setV : DivStage B C a.W where
  div := ((reD a.D Z).div)
  div_good := (a.V.div_good)
  jEE := (a.V.jEE)
  jEE_basis := (a.V.jEE_basis)
  jN := (a.V.jN)
  jN_basis := (a.V.jN_basis)
  Dall_eq := (a.V.Dall_eq)
  delP_eq := (a.V.delP_eq)
  nuIn := (a.V.nuIn)
  nuIn_inj := (a.V.nuIn_inj)
  nuIn_range := (a.V.nuIn_range)
  nuIn_jN := (a.V.nuIn_jN)
  nuIn_norm := (a.V.nuIn_norm)
  jEE_norm := (a.V.jEE_norm)

def reL : Late B C := ⟨a.W, setV a Z, (reStage a.st Z.Z), a.N, a.G⟩

set_option maxHeartbeats 4000000 in

def XL (X : HidaSetting a.D) : HidaSetting (reL a Z).D := (reX Z X)

set_option maxHeartbeats 4000000 in

theorem hL {X : HidaSetting a.D} (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D) :
    (XL a Z X).B.I = Formalism.L2.SG.InstExistsPf.instOf (reL a Z).D := (h)

set_option maxHeartbeats 4000000 in

def gdL {X : HidaSetting a.D} (G : GoodOp X) : GoodOp (XL a Z X) := ⟨(G.Rg), (G.Rg_spec)⟩

set_option maxHeartbeats 4000000 in

def tL (t : GA a.D (a.D.sp.Y 0)) : GA (reL a Z).D ((reL a Z).D.sp.Y 0) := (t)

set_option maxHeartbeats 4000000 in

def jL {X : HidaSetting a.D} {G : GoodOp X} (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) :
    (reL a Z).D.what₂.EE ≃ₗᵢ[ℂ] EEC (XL a Z X) (gdL a Z G) := (j)

set_option maxHeartbeats 4000000 in

def SameL (F₀ : ∀ u, Forms0 a.D u) (F₁ : ∀ u, Forms0 (reL a Z).D u) : Prop := SameForms0LevelsAndValues Z F₀ ((F₁))

variable {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

set_option maxHeartbeats 4000000 in

def eL (R : RealDat a.D A Ks) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) :
    letI := alg (reL a Z) iK; (reL a Z).D.what₂.EE →ₗ[ℂ] (real (reL a Z) R).HE.H := (eE)

set_option maxHeartbeats 4000000 in

def SAtL (R : RealDat a.D A Ks) (F : Face a.D A) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (F₁ : ∀ u, Forms0 (reL a Z).D u) : Type 1 :=
  letI := alg (reL a Z) iK; SAt (real (reL a Z) R) (face (reL a Z) F) (eL a Z R eE) F₁

set_option maxHeartbeats 4000000 in

def SAtL.pt {R : RealDat a.D A Ks} {F : Face a.D A} {eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H} {F₁ : ∀ u, Forms0 (reL a Z).D u}
    (s : SAtL a Z R F eE F₁) : GA (reL a Z).D ((reL a Z).D.sp.Y 0) := letI := alg (reL a Z) iK; SAt.t s

end PiLocalization₂

set_option maxHeartbeats 4000000 in

def MvSee : Prop := ∀ {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) (X : HidaSetting a.D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D)
    (t : GA a.D (a.D.sp.Y 0)), SeeAt R F X h t →
    letI := alg (reL a Z) iK; SeeAt (real (reL a Z) R) (face (reL a Z) F) (XL a Z X) (hL a Z h) (tL a Z t)

set_option maxHeartbeats 4000000 in

def MvEv : Prop := ∀ {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) (X : HidaSetting a.D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D)
    (G : GoodOp X) (t : GA a.D (a.D.sp.Y 0)) (c : ℝ), EvalTieT (MP R) R.ν0 R.fd0 (EP R F) X G (iotaX X h).toMulEquiv t c →
    letI := alg (reL a Z) iK
    EvalTieT (MP (real (reL a Z) R)) (real (reL a Z) R).ν0 (real (reL a Z) R).fd0 (EP (real (reL a Z) R) (face (reL a Z) F)) (XL a Z X)
      (gdL a Z G) (iotaX (XL a Z X) (hL a Z h)).toMulEquiv (tL a Z t) c

set_option maxHeartbeats 4000000 in

def MvRowJ : Prop := ∀ {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (X : HidaSetting a.D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf a.D)
    (G : GoodOp X) (t : GA a.D (a.D.sp.Y 0)) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC X G), RowJ R eE X h G t j →
    letI := alg (reL a Z) iK; RowJ (real (reL a Z) R) (eL a Z R eE) (XL a Z X) (hL a Z h) (gdL a Z G) (tL a Z t) (jL a Z j)

end GlobalTheory.Mem.SRe

end

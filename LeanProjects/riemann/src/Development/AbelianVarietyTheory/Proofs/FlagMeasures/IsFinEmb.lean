import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature

open MeasureTheory NumberField Matrix Finset
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StabUnfold

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

structure Sib (I : AutInst) where
  n : ℕ
  J : Matrix (Fin n) (Fin n) I.E
  J_herm : Formalism.UG.IsHerm (starRingEnd I.E) J
  J_det : J.det ≠ 0
  L : Submodule (𝓞 I.E) (Fin n → I.E)
  L_span : Submodule.span I.E (L : Set (Fin n → I.E)) = ⊤
  L_fg : L.FG
  L_dual : ∀ x : Fin n → I.E, x ∈ L ↔
    ∀ y ∈ L, Formalism.UG.hform (starRingEnd I.E) J y x ∈ (algebraMap (𝓞 I.E) I.E).range
  ε : InfinitePlace I.F → Fin n → Bool
  P : InfinitePlace I.F → Matrix (Fin n) (Fin n) ℂ
  P_unit : ∀ v, IsUnit (P v)
  P_spec : ∀ v, (P v)ᴴ * J.map (I.φ v) * P v = Formalism.REAL.Jm (ε v)

def Sib.self (I : AutInst) : Sib I :=
  ⟨I.n, I.J, I.J_herm, I.J_det, I.L, I.L_span, I.L_fg, I.L_dual, I.ε, I.P, I.P_unit, I.P_spec⟩

variable {I : AutInst}

def Sib.frames (D : Sib I) : AutInst :=
  GlobalTheory.AutInhab.ofFrames I.cm D.n D.J D.J_herm D.J_det D.L D.L_span D.L_fg D.L_dual D.ε I.φ I.φ_over D.P
    D.P_unit D.P_spec

@[reducible] def Sib.inst (D : Sib I) : AutInst where
  F := I.F
  E := I.E
  cm := I.cm
  n := D.n
  J := D.J
  J_herm := D.J_herm
  J_det := D.J_det
  L := D.L
  L_span := D.L_span
  L_fg := D.L_fg
  L_dual := D.L_dual
  ε := D.ε
  φ := I.φ
  φ_over := I.φ_over
  P := D.P
  P_unit := D.P_unit
  P_spec := D.P_spec
  topf := D.frames.topf
  topf_group := D.frames.topf_group
  topf_open := D.frames.topf_open
  topf_basis := D.frames.topf_basis

instance (D : Sib I) : TopologicalSpace D.inst.Gf := D.inst.topf
instance (D : Sib I) : IsTopologicalGroup D.inst.Gf := D.inst.topf_group
instance (D : Sib I) : MeasurableSpace D.inst.Gf := AutInst.instMeasurableSpaceGf D.inst
instance (D : Sib I) : BorelSpace D.inst.Gf := AutInst.instBorelSpaceGf D.inst

def IsPerp (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) : Prop :=
  D.n + 1 = I.n ∧ star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s ∧ star x ᵥ* (I.J * A) = 0 ∧ Aᴴ * I.J * A = D.J ∧
    x ∈ lamX I (1, xf) ∧ ∀ y : Fin D.n → I.E, y ∈ D.L ↔ A *ᵥ y ∈ lamX I (1, xf)

def afVec (I : AutInst) {m : ℕ} (x : Fin m → I.E) : Fin m → I.E ⊗[I.F] Af I.F :=
  fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)

def afMat (I : AutInst) {m k : ℕ} (A : Matrix (Fin m) (Fin k) I.E) : Matrix (Fin m) (Fin k) (I.E ⊗[I.F] Af I.F) :=
  A.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def infVec (I : AutInst) (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

def infMat (D : Sib I) (v : InfinitePlace I.F) (A : Matrix (Fin I.n) (Fin D.n) I.E) :
    Matrix (Fin I.n) (Fin D.n) ℂ :=
  (I.P v)⁻¹ * A.map (I.φ v) * D.P v

def IsFinEmb (D : Sib I) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (jf : D.inst.Gf →* I.Gf) :
    Prop :=
  ∀ g, I.fmat (jf g) *ᵥ afVec I x = afVec I x ∧ I.fmat (jf g) * afMat I A = afMat I A * D.inst.fmat g

def IsInfEmb (D : Sib I) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E)
    (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) : Prop :=
  ∀ v g, uMat (jv v g) *ᵥ infVec I v x = infVec I v x ∧ uMat (jv v g) * infMat D v A = infMat D v A * uMat g

def embA (D : Sib I) (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) (jf : D.inst.Gf →* I.Gf) :
    D.inst.GA →* I.GA where
  toFun g := (fun v => jv v (g.1 v), jf g.2)
  map_one' := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact map_one (jv v)
    · exact map_one jf
  map_mul' g h := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact map_mul (jv v) _ _
    · exact map_mul jf _ _

def gaussAt (I : AutInst) (x : Fin I.n → I.E) (g : I.GA) : ENNReal :=
  (∏ v, ENNReal.ofReal (gauss ((uMat (g.1 v))⁻¹ *ᵥ infVec I v x))) *
    {h : I.Gf | x ∈ lamX I (1, h)}.indicator 1 g.2

def stabF (I : AutInst) (x : Fin I.n → I.E) : Set I.GA :=
  {γ | γ ∈ I.GFset ∧ I.fmat γ.2 *ᵥ afVec I x = afVec I x}

def Ksub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

theorem coe_Ksub (I : AutInst) : (Ksub I : Set I.Gf) = I.Kset := rfl

end GlobalTheory.StabUnfold

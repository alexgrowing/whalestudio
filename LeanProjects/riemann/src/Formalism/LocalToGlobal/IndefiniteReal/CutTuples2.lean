import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalToGlobal.GlobalTheory.DivPassage

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure CrdV {Bs : DefBase K} (A : DefAmb Bs) where

  v0R : DefSub A → Bool → ∀ t, Submodule K (A.FR t)

  v0L : DefSub A → Bool → ∀ j t, Submodule K (A.FL j t)

  hR : ∀ t, A.FR t →ₗ⋆[K] A.FR t →ₗ[K] K

  hL : ∀ j t, A.FL j t →ₗ⋆[K] A.FL j t →ₗ[K] K

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

def bR (t : Bs.Tup) := Basis.ofVectorSpace K (A.FR t)

def bL (j : Bs.J) (t : Bs.Tup) := Basis.ofVectorSpace K (A.FL j t)

def KFormR : Prop :=
  ∀ t, LinearIndependent ℂ (fun k => X.jR t (bR t k)) ∧ Submodule.span ℂ (Set.range fun k => X.jR t (bR t k)) = ⊤

def KFormL : Prop :=
  ∀ j t, LinearIndependent ℂ (fun k => X.jL j t (bL j t k)) ∧
    Submodule.span ℂ (Set.range fun k => X.jL j t (bL j t k)) = ⊤

open Classical in

def opC (t : Bs.Tup) (i : A.OpR t) : Module.End ℂ (X.FC t) :=
  if h : LinearIndependent ℂ (fun k => X.jR t (bR t k)) ∧
      Submodule.span ℂ (Set.range fun k => X.jR t (bR t k)) = ⊤ then
    (Basis.mk h.1 h.2.ge).constr ℂ fun k => X.jR t (A.opR t i (bR t k))
  else 0

open Classical in

def opLC (j : Bs.J) (t : Bs.Tup) (i : A.OpL j t) : Module.End ℂ (X.FLC j t) :=
  if h : LinearIndependent ℂ (fun k => X.jL j t (bL j t k)) ∧
      Submodule.span ℂ (Set.range fun k => X.jL j t (bL j t k)) = ⊤ then
    (Basis.mk h.1 h.2.ge).constr ℂ fun k => X.jL j t (A.opL j t i (bL j t k))
  else 0

def KerStabR : Prop := ∀ t i (u : X.FC t), X.Θ t u = 0 → X.Θ t (X.opC t i u) = 0

def KerStabL : Prop := ∀ j t i (u : X.FLC j t), X.θ' j t u = 0 → X.θ' j t (X.opLC j t i u) = 0

def AdjClosedR : Prop := ∀ t i, ∃ i', X.opC t i' = LinearMap.adjoint (X.opC t i)

def AdjClosedL : Prop := ∀ j t i, ∃ i', X.opLC j t i' = LinearMap.adjoint (X.opLC j t i)

def JIsoR (cv : CrdV A) : Prop := ∀ t (x y : A.FR t), ⟪X.jR t x, X.jR t y⟫_ℂ = Bs.v0.embedding (cv.hR t x y)

def JIsoL (cv : CrdV A) : Prop := ∀ j t (x y : A.FL j t), ⟪X.jL j t x, X.jL j t y⟫_ℂ = Bs.v0.embedding (cv.hL j t x y)

def CutStable : Prop :=
  X.KFormR → X.KFormL → X.KerStabR → X.KerStabL → X.AdjClosedR → X.AdjClosedL → X.zs.Stable

section Level

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A) (b : Bool)

def V0C (t : Bs.Tup) : Submodule ℂ (X.FC t) := Submodule.span ℂ ((X.jR t) '' (cv.v0R X.zs b t : Set (A.FR t)))

def goodPartComplexPoints (j : Bs.J) (t : Bs.Tup) : Submodule ℂ (X.FLC j t) :=
  Submodule.span ℂ ((X.jL j t) '' (cv.v0L X.zs b j t : Set (A.FL j t)))

def IsoR : Prop :=
  ∀ t (x y : Fin ((lv (fc X.zs) b).dQ t) → K),
    ⟪X.jR t (cr.toR X.zs b t x), X.jR t (cr.toR X.zs b t y)⟫_ℂ =
      ((X.nP b : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc X.zs) b).XQ t) Bs.v0 x y

def CrdZ : Prop := ∀ t (x : Fin ((lv (fc X.zs) b).dQ t) → K), cr.toR X.zs b t x ∈ X.Z t

def CoordinatesInGoodPart : Prop := ∀ t (x : Fin ((lv (fc X.zs) b).dQ t) → K), cr.toR X.zs b t x ∈ cv.v0R X.zs b t

def RatLev : Prop :=
  ∀ t, Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) =
    LinearMap.range (LinearMap.adjoint (X.Θ t)) ⊓ X.V0C cv b t

def DnLev : Prop := ∀ t, (X.V0C cv b t).map (X.Θ t) ≤ X.EEl b

def UpLev : Prop := ∀ t, (X.EEl b).map (LinearMap.adjoint (X.Θ t)) ≤ X.V0C cv b t

def ThmBop : Prop :=
  ∀ t p, ∀ e ∈ X.EEp p ⊓ X.EEl b,
    X.Θ t (LinearMap.adjoint (X.Θ t) e) = ((X.κ Bs.v0 * ∏ j, X.lam j t p Bs.v0 : ℝ) : ℂ) • e

def PartsE : Prop :=
  (∀ p q, p ≠ q → ∀ e ∈ X.EEp p ⊓ X.EEl b, ∀ e' ∈ X.EEp q ⊓ X.EEl b, ⟪e, e'⟫_ℂ = 0) ∧
    (⨆ p, X.EEp p ⊓ X.EEl b) = X.EEl b

def CutRows : Prop :=
  (lv (fc X.zs) b).WF → X.H4pos → X.IsoR cr b → X.CrdZ cr b → X.CoordinatesInGoodPart cr cv b → X.RatLev cr cv b → X.DnLev cv b →
    X.UpLev cv b → X.ThmBop b → X.PartsE b → X.H2 cr b ∧ X.H4 cr b

def IsoL : Prop :=
  ∀ j t (x y : Fin ((lv (fc X.zs) b).dZ j t) → K),
    ⟪X.jL j t (cr.toL X.zs b j t x), X.jL j t (cr.toL X.zs b j t y)⟫_ℂ =
      ((X.nP b : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc X.zs) b).XT j t) Bs.v0 x y

def CrdZL : Prop := ∀ j t (x : Fin ((lv (fc X.zs) b).dZ j t) → K), cr.toL X.zs b j t x ∈ X.Zl j t

def LiftCoordinatesInGoodPart : Prop := ∀ j t (x : Fin ((lv (fc X.zs) b).dZ j t) → K), cr.toL X.zs b j t x ∈ cv.v0L X.zs b j t

def RatLevL : Prop :=
  ∀ j t, Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dZ j t) → K => X.jL j t (cr.toL X.zs b j t x)) =
    LinearMap.range (LinearMap.adjoint (X.θ' j t)) ⊓ X.goodPartComplexPoints cv b j t

def DnLevL : Prop := ∀ j t, (X.goodPartComplexPoints cv b j t).map (X.θ' j t) ≤ LinearMap.range (X.w0C b j)

def UpLevL : Prop := ∀ j t, (LinearMap.range (X.w0C b j)).map (LinearMap.adjoint (X.θ' j t)) ≤ X.goodPartComplexPoints cv b j t

def ThmAop : Prop :=
  ∀ j t p, ∀ w ∈ X.Wp j p ⊓ LinearMap.range (X.w0C b j),
    X.θ' j t (LinearMap.adjoint (X.θ' j t) w) = ((X.lam j t p Bs.v0 : ℝ) : ℂ) • w

def PartsW : Prop :=
  ∀ j, (∀ p q, p ≠ q → ∀ w ∈ X.Wp j p ⊓ LinearMap.range (X.w0C b j), ∀ w' ∈ X.Wp j q ⊓ LinearMap.range (X.w0C b j),
      ⟪w, w'⟫_ℂ = 0) ∧ (⨆ p, X.Wp j p ⊓ LinearMap.range (X.w0C b j)) = LinearMap.range (X.w0C b j)

def CutLifts : Prop :=
  (lv (fc X.zs) b).WF → X.H4pos → X.KForm b → X.IsoL cr b → X.CrdZL cr b → X.LiftCoordinatesInGoodPart cr cv b → X.RatLevL cr cv b →
    X.DnLevL cv b → X.UpLevL cv b → X.ThmAop b → X.PartsW b → X.H5 cr b ∧ X.ThmA cr b

def DimParts : Prop :=
  ∀ j p, Module.finrank ℂ (X.Wp j p ⊓ LinearMap.range (X.w0C b j) : Submodule ℂ (X.W j)) =
    Module.finrank ℂ (X.EEp p ⊓ X.EEl b : Submodule ℂ X.EE)

def CutDims : Prop :=
  (lv (fc X.zs) b).WF → X.H4pos → X.KForm b → X.EWnorm b → (lv (fc X.zs) b).Types → X.H2 cr b →
    X.RATmu cr b → X.H3 cr b → X.H5 cr b → X.RATth cr b → X.H3W cr b →
    X.PartsE b → X.PartsW b → X.DimParts b → (X.data cr b).DimensionsOfPartsAgree

end Level

section Pairing

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc)

open Classical in

def rinv {d n : ℕ} (P : Matrix (Fin d) (Fin n) K) : Matrix (Fin n) (Fin d) K :=
  if h : ∃ R : Matrix (Fin n) (Fin d) K, P * R = 1 then h.choose else 0

def Bdef (u : (fc X.zs).Dc.Mem) :
    (Fin ((fc X.zs).Dc.a u) → K) →ₗ[K] Module.Dual K (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → K) :=
  ((fc X.zs).Dc.Pt u Bs.μ0).compl₂ (rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVecLin

def colDef (ζ : (fc X.zs).Dc.Mem → Bs.Tup → K) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) : CxData.CxCol (fc := fc) X :=
  ⟨X.Bdef, ζ, sEE⟩

def BtVanish : Prop :=
  ∀ u φ F, F ∈ (fc X.zs).Df1.U Bs.μ0 → (fc X.zs).Dc.Pt u Bs.μ0 φ F = 0

def MatrixIdentityOffBase (ζ : (fc X.zs).Dc.Mem → Bs.Tup → K) : Prop :=
  ∀ u t, t ≠ Bs.μ0 → ∀ (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV t) → K),
    ζ u t * (fc X.zs).Dc.Pt u t φ F = X.Bdef u φ ((X.rowMat cr true t).mulVec (((fc X.zs).Df1.Pq t).mulVec F))

def ZetaOK (ζ : (fc X.zs).Dc.Mem → Bs.Tup → K) : Prop :=
  (∀ u, ζ u Bs.μ0 = 1) ∧ (∀ u t, ζ u t ≠ 0) ∧ ∀ u w, vw w (ζ u (X.μ w)) = 0

def CutPairing : Prop :=
  ∀ (ζ : (fc X.zs).Dc.Mem → Bs.Tup → K) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH),
    (fc X.zs).Df1.WF → X.H2 cr true → X.BtVanish (fc := fc) → X.MatrixIdentityOffBase cr ζ → X.ZetaOK ζ →
      (X.colOf cr (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).PairingFactorsThroughPeriods

end Pairing

section Tuples

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc)

def W1 (N : IndefNum Bs) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ j, (X.data cr false).Iw j Bs.μ0 w ≠ 0 ∨ (X.data cr false).Iw j Bs.μ0 (conjPl w) ≠ 0 ∨
    jw ((lv (fc X.zs) false).HT j Bs.μ0) w ((lv (fc X.zs) false).Tl j Bs.μ0) ≠ 0 ∨
    jw ((lv (fc X.zs) false).HT j Bs.μ0) (conjPl w) ((lv (fc X.zs) false).Tl j Bs.μ0) ≠ 0 ∨
    N.F0 w j ≠ 0 ∨ N.F0 (conjPl w) j ≠ 0

open Classical in

def MuDef (N : IndefNum Bs) (tw : HeightOneSpectrum (𝓞 K) → Bs.Tup) : Prop :=
  (∀ w, X.W1 cr N w → tw w ≠ Bs.μ0) ∧ (∀ w, X.W1 cr N w → tw (conjPl w) = tw w) ∧
    (∀ w, X.μ w = if X.W1 cr N w then tw w else Bs.μ0) ∧ ∀ w, w ∈ X.Tw ↔ X.W1 cr N w

def CutTuples (C CH : ℝ) : Prop :=
  ∀ tw, X.MuDef cr ((fc X.zs).Z.num C CH) tw → X.H0 ∧ (X.data cr false).Untwisted ((fc X.zs).Z.num C CH)

def CutTuples2 (C CH : ℝ) : Prop :=
  X.H0 → (∀ w, X.W1 cr ((fc X.zs).Z.num C CH) w → w ∈ X.Tw) → (X.data cr false).Untwisted ((fc X.zs).Z.num C CH)

end Tuples

section Passage

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc)

open Formalism.L2.GlobalTheoryTheory.DivPassage in

def Levels (N : IndefNum Bs) : Prop :=
  ∃ LA : LevelAmb K (X.data cr false).D (X.data cr true).D,
    LA.FramesG ∧ LA.LatG ∧ LA.EmbAt LA.ι0 LA.ep0 LA.h0 (X.data cr false).XE ∧
    LA.EmbAt LA.ι1 LA.ep1 LA.h1 (X.data cr true).XE ∧ LA.SandAt LA.ι0 LA.ep0 LA.h0 (X.data cr false).RR ∧
    LA.SandAt LA.ι1 LA.ep1 LA.h1 (X.data cr true).RR ∧ LA.Sizes N.la ∧ LA.Ranks ∧ LA.Deg0 ∧ LA.Deg1 ∧
    LA.MaxT ∧ LA.Mult N.de ∧ LA.RowsG

def CutPassage [IsTotallyComplex K] (C CH : ℝ) : Prop :=
  X.Levels cr ((fc X.zs).Z.num C CH) → Passage ((fc X.zs).Z.num C CH) (X.data cr false) (X.data cr true)

end Passage

end CxData

end Formalism.IndefR.Cx

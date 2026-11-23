import Formalism.LocalToGlobal.GlobalTheory.FamCol
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.Divisibility.LiftLat

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRows

open Formalism Formalism.HN Formalism.L2.Col Formalism.L2.Indef Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.GlobalTheoryTheory.FamCol

section Link

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} {Bs : DefBase K} {Df : DefSide Bs}

structure ColLink (C : ColObj K I) (Dc : DefCols Df) where

  wU : I → Dc.Mem

  e : ∀ u, (C.M u).ι ≃ Fin (Dc.a (wU u))

namespace ColLink

variable {C : ColObj K I} {Dc : DefCols Df} (L : ColLink C Dc)

def eM (u : I) : (Fin (Dc.a (L.wU u)) → K) ≃ₗ[K] (C.M u).V :=
  ((C.M u).b.reindex (L.e u)).equivFun.symm

def NuD (u : I) : Submodule (𝓞 K) (Fin (Dc.a (L.wU u)) → K) :=
  (C.Nu u).comap (((L.eM u : (Fin (Dc.a (L.wU u)) → K) →ₗ[K] (C.M u).V)).restrictScalars (𝓞 K))

def Tied : Prop :=
  ∀ u (v : InfinitePlace K), Dc.Xc (L.wU u) v = Matrix.reindex (L.e u) (L.e u) ((C.M u).X v)

end ColLink

open Classical in

def sgD (C : ColObj K I) (u : I) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  if w ∈ C.supp then (eW w : ℝ) * C.sg u w else 0

end Link

section Rows

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}
  {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}

structure RowExt (C : ColObj K I) (D : ℕ) where

  κ₁ : Type
  [i1 : Fintype κ₁]
  [i2 : DecidableEq κ₁]

  Bf : ∀ u, Matrix (Fin D ⊕ κ₁) (C.Mf u).ι ℂ

  γ : I → ℝ

  η0 : ℝ

  η1 : ℝ

  e0 : ℝ

attribute [instance] RowExt.i1 RowExt.i2

def colB {C : ColObj K I} (L : ColLink C Dc) (S : IndefCols Df Dc Sp N) (u : I) :
    (C.M u).V →ₗ[K] Module.Dual K (Fin S.D → K) :=
  S.col.B (L.wU u) ∘ₗ ((L.eM u).symm : (C.M u).V →ₗ[K] (Fin (Dc.a (L.wU u)) → K))

def rowArg (C : ColObj K I) (L : ColLink C Dc) (S : IndefCols Df Dc Sp N) (X : RowExt C S.D) (hu : I → ℝ) :
    RowArg C where
  Wd := Module.Dual K (Fin S.D → K)
  κ := Fin S.D
  κ₁ := X.κ₁
  b' := (Pi.basisFun K (Fin S.D)).dualBasis
  X' := dualFrame S.XE
  cc := dualLat S.RR
  B := colB L S
  v := Bs.v0
  Y := fun u => (C.M u).X Bs.v0
  Y' := dualFrame S.XE Bs.v0
  Ball := fun u => X.Bf u * C.Vr u Bs.v0
  γ := X.γ
  Bf := X.Bf
  h := fun u => hu u - meanLog S.κ
  η0 := X.η0
  η1 := X.η1
  e0 := X.e0

structure RowIn (S : IndefCols Df Dc Sp N) (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
    (sg : HeightOneSpectrum (𝓞 K) → ℝ) (hu : ℝ) where

  Nu_lat : Submodule.IsLattice K Nu

  val2 : ∀ w, ∀ φ ∈ Nu, ∀ F ∈ Df.Mt (S.μ w),
    Dc.Pt u (S.μ w) φ F = 0 ∨ sg w ≤ (vw w (Dc.Pt u (S.μ w) φ F) : ℝ)

  Xc_unit : ∀ v, IsUnit (Dc.Xc u v).det

  X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ

  base_matrix_det_unit : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding

  pU : InfinitePlace K → ℝ

  pU_bd : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u)
    (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v (Dc.Pt u Bs.μ0) ≤ pU v

  hbound : (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (pU v ^ 2) - ∑ j, N.l6 j ≤ hu

structure ExtHyp [Fintype I] (C : ColObj K I) (L : ColLink C Dc) (S : IndefCols Df Dc Sp N) (X : RowExt C S.D)
    (sg : ℝ) : Prop where
  block : ∀ u (k : Fin S.D) (j : (C.M u).ι), (X.Bf u * C.Vr u Bs.v0) (Sum.inl k) j =
    ((dualFrame S.XE Bs.v0)⁻¹ * (LinearMap.toMatrix (C.M u).b (Pi.basisFun K (Fin S.D)).dualBasis
      (colB L S u)).map Bs.v0.embedding * (C.M u).X Bs.v0) k j
  γ : ∀ u, 0 < X.γ u
  sg_pos : 0 < sg
  sg_le : sg ≤ 1 / 20
  proviso : C.Dstar / sg ≤ ∑ u, (Fintype.card (C.Mf u).ι : ℝ)
  η0_ge : -1 ≤ X.η0
  η0_le : X.η0 ≤ sg / 2
  η1_le : X.η1 ≤ sg / 2
  exponent_bound_ter : 0 ≤ X.e0
  sqrt_error_le_half : Real.sqrt X.e0 ≤ sg / 2
  inputS : Formalism.LFunctionChainParameters.MatrixLatticeEstimates.InputSG X.Bf X.γ C.Dstar X.η0 X.η1 X.e0

end Rows

def LineHypothesesOfColumnExtension : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) [Fintype I]
    {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
    (C : ColObj K I) (L : ColLink C Dc) (S : IndefCols Df Dc Sp N) (X : RowExt C S.D) (hu : I → ℝ) (sg : ℝ),
    Df.WF → L.Tied → (∀ u, Nonempty (RowIn S (L.wU u) (L.NuD u) (sgD C u) (hu u))) → ExtHyp C L S X sg →
    RowHyp C (rowArg C L S X hu) sg

def faceC {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) : DefSub A.fam.amb → DefFace A.fam.base :=
  fun Zs => ⟨A.side P0 ψ0 Zs, A.side P1 ψ1 Zs, Dc Zs, Sp Zs, Zsc Zs⟩

def LineHypothesesConcretePackage : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) [Fintype I]
    {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (A : FamIn K G Pl0 T m) (s : ℕ), A.fam.Ok s → A.fam.TypesSep →
    ∀ (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (Cn CH : ℝ)
    (Pk : IndefPkg A.fam.amb (faceC A P0 ψ0 P1 ψ1 Dc Sp Zsc) Cn CH)
    (C : ColObj K I) (L : ColLink C (Dc Pk.Zs)) (X : RowExt C Pk.core.cols.D) (hu : I → ℝ) (sg : ℝ),
    L.Tied → (∀ u, Nonempty (RowIn Pk.core.cols (L.wU u) (L.NuD u) (sgD C u) (hu u))) →
    ExtHyp C L Pk.core.cols X sg →
    RowHyp C (rowArg C L Pk.core.cols X hu) sg

end Formalism.L2.GlobalTheoryTheory.FamRows

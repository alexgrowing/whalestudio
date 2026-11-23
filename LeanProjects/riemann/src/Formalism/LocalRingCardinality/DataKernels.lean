import Mathlib
import Formalism.LocalRingCardinality.Params
import Formalism.ThetaLiftIndependence.Statement

namespace Formalism.BasicNotions

open scoped BigOperators

def mulFun {Y : Type*} (g : Y → ℂ) : (Y → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ := fun y => g y * φ y
  map_add' φ ψ := by funext y; simp [mul_add]
  map_smul' c φ := by funext y; simp; ring

structure ColumnChain (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) where

  cls : ℕ → Type
  [clsFin : ∀ i, Fintype (cls i)]

  stab : ∀ i, cls i → Type
  [stabGrp : ∀ i c, Group (stab i c)]
  [stabFin : ∀ i c, Finite (stab i c)]

  DGam : ℕ
  DGam_pos : 0 < DGam
  dvd_DGam : ∀ i, i ≤ R.m → ∀ c, Nat.card (stab i c) ∣ DGam

  Y : ℕ → Type

  de : ∀ i, Y i → ι → ℂ
  de_ne : ∀ i y τ, de i y τ ≠ 0

  rhoDet : ∀ i, cls i → ℂ

  rhoDet' : ∀ i, cls (i + 1) → ℂ

  rho_norm : ∀ i, i < R.m → ∀ c, ‖rhoDet i c‖ = 1
  rho'_norm : ∀ i, i < R.m → ∀ c, ‖rhoDet' i c‖ = 1

  unf : ∀ i, cls i → cls (i + 1) → ((Y i → ℂ) →ₗ[ℂ] (Y (i + 1) → ℂ))

  sSharp : ℕ → ι → ℤ
  sSharp_eq : ∀ (i : ℕ) (h : i < R.m) (τ : ι),
    (sSharp i τ : ℚ) = sExp' R ((hc τ).e ⟨i, h⟩) (i + 1)

  sDiv : ℕ → ι → ℤ
  sDiv_eq : ∀ (i : ℕ) (h : i < R.m) (τ : ι),
    (sDiv i τ : ℚ) = sExp R ((hc τ).e ⟨i, h⟩) (i + 1)

namespace ColumnChain

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)

attribute [instance] ColumnChain.clsFin ColumnChain.stabGrp ColumnChain.stabFin

noncomputable def wt (i : ℕ) (c : C.cls i) : ℂ := ((Nat.card (C.stab i c) : ℕ) : ℂ)⁻¹

noncomputable def sharp (i : ℕ) : (C.Y i → ℂ) →ₗ[ℂ] (C.Y i → ℂ) :=
  mulFun (fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ))

noncomputable def divDe (i : ℕ) : (C.Y (i + 1) → ℂ) →ₗ[ℂ] (C.Y (i + 1) → ℂ) :=
  mulFun (fun y' => (∏ τ, (C.de (i + 1) y' τ) ^ (C.sDiv i τ))⁻¹)

noncomputable def Kmap (i : ℕ) (L : C.cls i) (L' : C.cls (i + 1)) :
    (C.Y i → ℂ) →ₗ[ℂ] (C.Y (i + 1) → ℂ) :=
  (C.rhoDet i L * C.rhoDet' i L') • ((C.divDe i).comp ((C.unf i L L').comp (C.sharp i)))

noncomputable def K (i : ℕ) (φ : C.cls i → C.Y i → ℂ) : C.cls (i + 1) → C.Y (i + 1) → ℂ :=
  Formalism.ThetaLiftIndependence.kerOpM (C.wt i) (C.Kmap i) φ

noncomputable def col (φ : C.cls 0 → C.Y 0 → ℂ) : C.cls R.m → C.Y R.m → ℂ :=
  Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap R.m φ

noncomputable def KD : (j : ℕ) → (C.cls (j - 1) → C.Y (j - 1) → ℂ) → C.cls j → C.Y j → ℂ
  | 0, φ => φ
  | j + 1, φ => C.K j φ

end ColumnChain

structure TupleData {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R}
    (C : ColumnChain R ι hc) where
  rhoDet : ∀ i, C.cls i → ℂ
  rhoDet' : ∀ i, C.cls (i + 1) → ℂ
  rho_norm : ∀ i, i < R.m → ∀ c, ‖rhoDet i c‖ = 1
  rho'_norm : ∀ i, i < R.m → ∀ c, ‖rhoDet' i c‖ = 1
  unf : ∀ i, C.cls i → C.cls (i + 1) → ((C.Y i → ℂ) →ₗ[ℂ] (C.Y (i + 1) → ℂ))

namespace ColumnChain

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R}

def twist (C : ColumnChain R ι hc) (T : TupleData C) : ColumnChain R ι hc :=
  { C with rhoDet := T.rhoDet, rhoDet' := T.rhoDet', rho_norm := T.rho_norm,
           rho'_norm := T.rho'_norm, unf := T.unf }

def ownData (C : ColumnChain R ι hc) : TupleData C :=
  ⟨C.rhoDet, C.rhoDet', C.rho_norm, C.rho'_norm, C.unf⟩

noncomputable def colTw (C : ColumnChain R ι hc) (T : TupleData C) (φ : C.cls 0 → C.Y 0 → ℂ) :
    C.cls R.m → C.Y R.m → ℂ :=
  (C.twist T).col φ

end ColumnChain

structure ColumnsAtT (R : Ranks) {ι : Type} [Fintype ι] {hc : ι → HCParam R}
    (C : ColumnChain R ι hc) where

  T : ℕ
  T_prime : T.Prime

  vT : Type
  [vTFin : Fintype vT]
  card_vT : Fintype.card vT = R.f

  Fv : vT → Type
  [FvField : ∀ v, Field (Fv v)]
  [FvFin : ∀ v, Fintype (Fv v)]
  [FvDec : ∀ v, DecidableEq (Fv v)]

  card_Fv : ∀ v, Fintype.card (Fv v) = T

  psiT : ∀ v, AddChar (Fv v) ℂ
  psiT_ne : ∀ v, psiT v ≠ 1

  rhoT : ∀ v, (Fv v)ˣ →* ((C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls 0 → C.Y 0 → ℂ))

  Mu0 : Submodule ℂ (C.cls 0 → C.Y 0 → ℂ)
  Mu0_fd : FiniteDimensional ℂ Mu0
  Mu0_stable : ∀ v c, Mu0.map (rhoT v c) ≤ Mu0

  duStar : ℕ
  duStar_pos : 0 < duStar

  Dstar : ℝ
  Dstar_pos : 0 < Dstar

  GamP : ℝ
  one_lt_gammaP : 1 < GamP

namespace ColumnsAtT

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc}
  (A : ColumnsAtT R C)

attribute [instance] ColumnsAtT.vTFin ColumnsAtT.FvField ColumnsAtT.FvFin ColumnsAtT.FvDec

noncomputable def Nm (v : A.vT) : (C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls 0 → C.Y 0 → ℂ) :=
  ∑ c : (A.Fv v)ˣ, A.rhoT v c

noncomputable def Mram : Submodule ℂ (C.cls 0 → C.Y 0 → ℂ) :=
  A.Mu0 ⊓ ⨅ v, LinearMap.ker (A.Nm v)

noncomputable def du : ℕ := Module.finrank ℂ A.Mram

noncomputable def gauss (v : A.vT) : (C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls 0 → C.Y 0 → ℂ) :=
  Formalism.ThetaLiftIndependence.gaussOp (A.psiT v) (A.rhoT v)

noncomputable def Xu : ℝ := (A.Dstar / A.duStar) ^ ((1 : ℝ) / (R.f * R.k))

noncomputable def Tstar : ℝ := A.Xu * A.GamP ^ (-(2 : ℝ) / (R.f * R.k))

end ColumnsAtT

structure PeriodMap (R : Ranks) {ι : Type} [Fintype ι] {hc : ι → HCParam R}
    (C : ColumnChain R ι hc) where

  Mt : Type
  [MtAcg : AddCommGroup Mt]
  [MtMod : Module ℂ Mt]

  Wz : Type
  [WzAcg : AddCommGroup Wz]
  [WzMod : Module ℂ Wz]

  evz : (C.cls R.m → C.Y R.m → ℂ) →ₗ[ℂ] Wz

  Wrow : Type
  [WrowAcg : AddCommGroup Wrow]
  [WrowMod : Module ℂ Wrow]

  lowerMap : Wz →ₗ[ℂ] Wrow

  period : Wrow →ₗ[ℂ] Mt →ₗ[ℂ] ℂ

namespace PeriodMap

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc}
  (P : PeriodMap R C)

attribute [instance] PeriodMap.MtAcg PeriodMap.MtMod PeriodMap.WzAcg PeriodMap.WzMod
  PeriodMap.WrowAcg PeriodMap.WrowMod

noncomputable def Ptil (ψ : C.cls R.m → C.Y R.m → ℂ) (F : P.Mt) : ℂ :=
  P.period (P.lowerMap (P.evz ψ)) F

noncomputable def PtilCol (φ : C.cls 0 → C.Y 0 → ℂ) (F : P.Mt) : ℂ := P.Ptil (C.col φ) F

end PeriodMap

def FactWtPos : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc) i c,
    0 < Nat.card (C.stab i c)

def ColumnChain.StabZero {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) : Prop :=
  ∀ c, Subsingleton (C.stab 0 c)

def FactWtZero : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc), C.StabZero → ∀ c,
    C.wt 0 c = 1

def FactWtInt : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc) i, i ≤ R.m →
    ∀ c, ∃ z : ℤ, (C.DGam : ℂ) * C.wt i c = z

def bridge_KD_succ : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc)
    (j : ℕ) (φ : C.cls j → C.Y j → ℂ), C.KD (j + 1) φ = C.K j φ

def bridge_thl_index : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc)
    (φ : C.cls 0 → C.Y 0 → ℂ) (i : ℕ),
    Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap (i + 1) φ = C.K i (Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap i φ)

def FactSDivSharp : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc)
    (i : ℕ), i < R.m → ∀ τ, ((C.sDiv i τ - C.sSharp i τ : ℤ) : ℚ) = ((R.t : ℚ) + 1) / 2

def FactEInt : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (_C : ColumnChain R ι hc)
    (j : Fin R.m) (τ : ι), ((hc τ).e j).den = 1

def FactDuLe : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc)
    (A : ColumnsAtT R C), A.du ≤ (haveI := A.Mu0_fd; Module.finrank ℂ A.Mu0)

def FactGaussRam : Prop :=
  ∀ (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) (C : ColumnChain R ι hc)
    (A : ColumnsAtT R C) (v : A.vT) (x : C.cls 0 → C.Y 0 → ℂ), A.Nm v x = 0 →
    Formalism.ThetaLiftIndependence.gaussOp (A.psiT v) (A.rhoT v) (Formalism.ThetaLiftIndependence.gaussOpDual (A.psiT v) (A.rhoT v) x) =
      (Fintype.card (A.Fv v) : ℂ) • x

def bridge_autL_not_column : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V),
    (LinearEquiv.neg K : V ≃ₗ[K] V) ∈ Formalism.ThetaLiftIndependence.autL h L

end Formalism.BasicNotions

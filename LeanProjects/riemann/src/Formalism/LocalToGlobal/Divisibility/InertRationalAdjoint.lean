import Mathlib
import Formalism.LocalToGlobal.Divisibility.RowLat

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

structure InertDat3 {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (I0 Ty : Type) where

  PlI : Type

  plI : PlI → I0

  opI : PlI × Ty → Module.End K B.S.Forms

abbrev Typ3 (K Pl0 I0 Ty : Type) [Field K] : Type := (Pl0 → K[X]) × (I0 × Ty → K)

namespace InertDat3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}
  {B : BlockDat K G Pl0} (D : InertDat3 B I0 Ty) (ℓ : Lvl K G)

abbrev OpIx : Type := (B.Pl × ℕ) ⊕ (D.PlI × Ty)

def opAll : D.OpIx → Module.End K B.S.Forms := Sum.elim B.op D.opI

def HasRes3 (p : Typ3 K Pl0 I0 Ty) (x : D.OpIx → K) : Prop :=
  B.HasRes p.1 (fun i => x (Sum.inl i)) ∧ ∀ k : D.PlI × Ty, x (Sum.inr k) = p.2 (D.plI k.1, k.2)

def inertTypeEigenspaceSum (p : Typ3 K Pl0 I0 Ty) : Submodule K B.S.Forms := Col.eigSum D.opAll (D.HasRes3 p)

def resSet3 (X : Finset (G → K)) : Set (Typ3 K Pl0 I0 Ty) :=
  {p | (∀ P0, P0 ∉ Set.range B.pl → p.1 P0 = 1) ∧ (∀ P0, P0 ∉ Set.range D.plI → ∀ y, p.2 (P0, y) = 0) ∧
    B.inV0 (Lvl.full X) (D.inertTypeEigenspaceSum p) ≠ ⊥}

open Classical in

def ixFin3 (X : Finset (G → K)) : Finset (Typ3 K Pl0 I0 Ty) :=
  if h : (D.resSet3 X).Finite then h.toFinset else ∅

def part3 (Z : Submodule K B.S.Forms) (p : Typ3 K Pl0 I0 Ty) : Submodule K (Fin (B.dZ ℓ Z) → K) :=
  (B.inV0 ℓ (D.inertTypeEigenspaceSum p)).comap (B.zE ℓ Z).mulVecLin

def DiffAt (p p' : Typ3 K Pl0 I0 Ty) : Prop :=
  (∃ P : B.Pl, p.1 (B.pl P) ≠ p'.1 (B.pl P)) ∨ ∃ k : D.PlI × Ty, p.2 (D.plI k.1, k.2) ≠ p'.2 (D.plI k.1, k.2)

structure Ok3 : Prop where

  comm : Col.PairComm D.opAll

  split : Col.SplitOver D.opI

  opG : ∀ k g, Commute (D.opI k) (B.r g)

  plI_inj : Function.Injective D.plI

structure InertRationalAdjoint : Prop where

  rat : ∀ k a b, LinearMap.toMatrix B.S.basis B.S.basis (D.opI k) a b ∈ cmMax K

  adj : ∀ k, ∃ k', ∀ f g : B.S.Forms,
    B.S.csum (D.opI k f : B.S.Cl → B.S.V) (g : B.S.Cl → B.S.V) =
      B.S.csum (f : B.S.Cl → B.S.V) (D.opI k' g : B.S.Cl → B.S.V)

structure OkLat3 : Prop where

  nab : ∀ k, ∀ x ∈ B.S.nabLat, (LinearMap.toMatrix B.S.basis B.S.basis (D.opI k)).mulVec x ∈ B.S.nabLat

  del : ∀ k, ∀ x ∈ B.S.delLat, (LinearMap.toMatrix B.S.basis B.S.basis (D.opI k)).mulVec x ∈ B.S.delLat

def Stable3 (Z : Submodule K B.S.Forms) : Prop := ∀ i, Z ≤ Z.comap (D.opAll i)

end InertDat3

structure DefFam3 (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
    (Pl0 I0 Ty T J : Type) where

  F : DefFam K G Pl0 T J

  RI : ∀ t, InertDat3 (F.R t) I0 Ty

  LI : ∀ j t, InertDat3 (F.L j t) I0 Ty

  trI : J → (I0 × Ty → K) → I0 × Ty → K

namespace DefFam3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 I0 Ty T J : Type} [Fintype J] (F3 : DefFam3 K G Pl0 I0 Ty T J)

def tr3 (j : J) (p : Typ3 K Pl0 I0 Ty) : Typ3 K Pl0 I0 Ty := (F3.F.tr j p.1, F3.trI j p.2)

@[reducible] def base3 : DefBase K where
  K0 := cmMax K
  v0 := F3.F.v0
  Tup := T
  μ0 := F3.F.μ0
  Ix := ↥((F3.RI F3.F.μ0).ixFin3 F3.F.X)
  fIx := inferInstance
  J := J
  fJ := inferInstance

@[reducible] def amb3 : DefAmb F3.base3 where
  FR t := (F3.F.R t).S.Forms
  aR _ := inferInstance
  mR _ := inferInstance
  OpR t := (F3.RI t).OpIx ⊕ G
  opR t := Sum.elim (F3.RI t).opAll fun g => (F3.F.R t).r g
  ZHR t := (F3.F.R t).ZHg F3.F.X
  FL j t := (F3.F.L j t).S.Forms
  aL _ _ := inferInstance
  mL _ _ := inferInstance
  OpL j t := (F3.LI j t).OpIx ⊕ G
  opL j t := Sum.elim (F3.LI j t).opAll fun g => (F3.F.L j t).r g
  ZHL j t := (F3.F.L j t).ZHg F3.F.X

def toSub2 (Zs : DefSub F3.amb3) : DefSub F3.F.amb := ⟨Zs.Z, Zs.Zl⟩

def side3 (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F3.amb3) : DefSide F3.base3 where
  nV t := (F3.F.R t).nV (F3.F.lvl P ψ)
  HV t := (F3.F.R t).HV (F3.F.lvl P ψ)
  Mt t := (F3.F.R t).Mt (F3.F.lvl P ψ)
  dQ t := (F3.F.R t).dZ (F3.F.lvl P ψ) (Zs.Z t)
  Pq t := (F3.F.R t).Pq (F3.F.lvl P ψ) (Zs.Z t)
  XQ t := (F3.F.R t).XQ (F3.F.lvl P ψ) (Zs.Z t)
  Qp t p := (F3.RI t).part3 (F3.F.lvl P ψ) (Zs.Z t) p.1
  dZ j t := (F3.F.L j t).dZ (F3.F.lvlA P ψ) (Zs.Zl j t)
  HT j t := (F3.F.L j t).HZ (F3.F.lvlA P ψ) (Zs.Zl j t)
  XT j t := (F3.F.L j t).XQ (F3.F.lvlA P ψ) (Zs.Zl j t)
  Tl j t := (F3.F.L j t).Tl (F3.F.lvlA P ψ) (Zs.Zl j t)
  Zp j t p := (F3.LI j t).part3 (F3.F.lvlA P ψ) (Zs.Zl j t) (F3.tr3 j p.1)

structure Ok3 (s : ℕ) : Prop where

  ok2 : F3.F.Ok s

  what₂ : ∀ t, (F3.RI t).Ok3

  lifts : ∀ j t, (F3.LI j t).Ok3

def IsType3 {B : BlockDat K G Pl0} (D : InertDat3 B I0 Ty) (f : Typ3 K Pl0 I0 Ty → Typ3 K Pl0 I0 Ty) (x : D.OpIx → K) : Prop :=
  ∃ p ∈ (F3.RI F3.F.μ0).ixFin3 F3.F.X, D.HasRes3 (f p) x

def SameTypes3 (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F3.amb3) : Prop :=
  ∀ j, (F3.F.L j F3.F.μ0).Z0 (F3.F.lvlA P ψ) (Zs.Zl j F3.F.μ0) ≤
    (F3.F.L j F3.F.μ0).inV0 (F3.F.lvlA P ψ) (Col.eigSum (F3.LI j F3.F.μ0).opAll (F3.IsType3 (F3.LI j F3.F.μ0) (F3.tr3 j)))

def TypesSep3 : Prop :=
  ∀ p ∈ (F3.RI F3.F.μ0).ixFin3 F3.F.X, ∀ p' ∈ (F3.RI F3.F.μ0).ixFin3 F3.F.X, p ≠ p' →
    ∀ j, (F3.LI j F3.F.μ0).DiffAt (F3.tr3 j p) (F3.tr3 j p')

end DefFam3

end Formalism.L2.DIV

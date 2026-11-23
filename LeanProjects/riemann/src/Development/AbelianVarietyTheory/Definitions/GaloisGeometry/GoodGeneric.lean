import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

structure InertJunk {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (A3 : FamIn3 K G Pl0 I0 (List ℕ) T m) : Prop where
  R : ∀ t Q s, A3.heckeRI t (Q, s) = 0 ∨
    ∃ s', Formalism.L2.Col.InertTypeOk (A3.A.r + m * A3.A.t) s' ∧ A3.heckeRI t (Q, s) = A3.heckeRI t (Q, s')
  L : ∀ j t Q s, A3.heckeLI j t (Q, s) = 0 ∨
    ∃ s', Formalism.L2.Col.InertTypeOk (A3.A.r + A3.A.t) s' ∧ A3.heckeLI j t (Q, s) = A3.heckeLI j t (Q, s')

def GoodGeneric {K : Type} [Field K] (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ χ ∈ X, chiIdem χ * lvlIdem P ψ ≠ 0

def TrISepWith (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)
    (tr : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL) : Prop :=
  ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) →
      ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2)

variable {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure RowDict (R : RealDat3 D A3 Ks) (t : T) (pl : (A3.rowI t).OpIx → Pl D.host.E)
    (cX c0 : (A3.rowI t).OpIx → List ℤ →₀ ℂ) : Prop where
  good : ∀ i, Good R.toRealDat t (pl i)
  op : ∀ h, IsOpsX R.toRealDat t h → ∀ i x, R.jX t ((A3.rowI t).opAll i x) = h (pl i) (cX i) (R.jX t x)
  mat : ∀ i, MatchE R.toRealDat t (pl i) (cX i) (c0 i)

structure LiftDict (R : RealDat3 D A3 Ks) (j : Fin D.R.m) (t : T) (pl : (A3.liftI j t).OpIx → Pl D.host.E)
    (cV cW : (A3.liftI j t).OpIx → List ℤ →₀ ℂ) : Prop where
  good : ∀ i, Good R.toRealDat t (pl i)
  op : ∀ h, IsOpsV R.toRealDat j t h → ∀ i x, R.jV j t ((A3.liftI j t).opAll i x) = h (pl i) (cV i) (R.jV j t x)
  mat : ∀ i, MatchW R.toRealDat j t (pl i) (cV i) (cW i)

def labW (j : Fin D.R.m) {I : Type} (pl : I → Pl D.host.E) (cW : I → List ℤ →₀ ℂ) (c : Pl D.host.E → List ℤ → ℂ) : I → ℂ :=
  fun i => evC (Wc D j) (pl i) (c (pl i)) (cW i)

end GlobalTheory.Hk3

end

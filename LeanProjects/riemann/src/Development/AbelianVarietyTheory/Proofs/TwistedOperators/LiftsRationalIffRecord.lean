import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatThOfLiftTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormsBasisInjective
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention

noncomputable section

open Module NumberField
open scoped InnerProductSpace

namespace GlobalTheory.LiftTestCompare

section Lin

open Matrix

variable {K : Type} [Field K] (σ : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

def FunTest (S : Set W) : Prop :=
  ∃ (N : ℕ) (ψ : Fin N → Module.Dual ℂ W), (∀ w, (∀ i, ψ i w = 0) → w = 0) ∧ ∀ s ∈ S, ∀ i, ψ i s ∈ Set.range σ

def SpanTest (S : Set W) : Prop :=
  ∃ (m : ℕ) (v : Fin m → W), LinearIndependent ℂ v ∧ ∀ s ∈ S, ∃ a : Fin m → K, s = ∑ i, σ (a i) • v i

end Lin

section Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

def liftsAll (j : Bs.J) : Set (X.W j) := {w | ∃ (t : Bs.Tup) (x : A.FL j t), X.θ' j t (X.jL j t x) = w}

def liftsAt (j : Bs.J) (t : Bs.Tup) : Set (X.W j) := {w | ∃ x : A.FL j t, X.θ' j t (X.jL j t x) = w}

def levelBasis (b : Bool) (j : Bs.J) : Set (X.W j) := Set.range fun k : Fin (X.dW b j) => X.w0C b j (Pi.single k 1)

def LevelIn (b : Bool) (V : ∀ j t, Submodule K (A.FL j t)) : Prop :=
  ∀ j t, ∀ x ∈ V j t, X.θ' j t (X.jL j t x) ∈ LinearMap.range (X.w0C b j)

theorem liftTest_of_liftTestB {b : Bool} (h : LiftTestB X b) : LiftTest X := fun j => by
  obtain ⟨N, ψ, h1, h2, -⟩ := h j
  exact ⟨N, ψ, h1, h2⟩

end Cx

section Real

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.TwistPlacesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

end Real

section ArchimedeanLeafBounds

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Rat GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase GlobalTheory.TwistPlacesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)

theorem toCx3_liftTestB (b : Bool) :
    LiftTestB (R.toCx3 F) b ↔ LiftTestB (cxPhase R.toRealDat F.lv2 fun j => cj (twAt D.what₂.embLL A3.A.v0) (R.phs j)) b := by
  rw [cxPhase_eq]
  simp only [cj_cj]
  exact Iff.rfl

end ArchimedeanLeafBounds

end GlobalTheory.LiftTestCompare

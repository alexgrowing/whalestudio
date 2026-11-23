import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2

open Module NumberField
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Rat

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

def RowTest : Prop :=
  ∃ (N : ℕ) (ψ : Fin N → Module.Dual ℂ X.EE), (∀ e, (∀ i, ψ i e = 0) → e = 0) ∧
    ∀ t i (x : A.FR t), ψ i (X.Θ t (X.jR t x)) ∈ Set.range Bs.v0.embedding

def LiftTest : Prop :=
  ∀ j, ∃ (N : ℕ) (ψ : Fin N → Module.Dual ℂ (X.W j)), (∀ w, (∀ i, ψ i w = 0) → w = 0) ∧
    ∀ t i (x : A.FL j t), ψ i (X.θ' j t (X.jL j t x)) ∈ Set.range Bs.v0.embedding

def LiftTestB (b : Bool) : Prop :=
  ∀ j, ∃ (N : ℕ) (ψ : Fin N → Module.Dual ℂ (X.W j)), (∀ w, (∀ i, ψ i w = 0) → w = 0) ∧
    (∀ t i (x : A.FL j t), ψ i (X.θ' j t (X.jL j t x)) ∈ Set.range Bs.v0.embedding) ∧
    ∀ i (k : Fin (X.dW b j)), ψ i (X.w0C b j (Pi.single k 1)) ∈ Set.range Bs.v0.embedding

def perpR (cv : CrdV A) (t : Bs.Tup) (S : Submodule K (A.FR t)) : Submodule K (A.FR t) :=
  ⨅ x ∈ S, LinearMap.ker (cv.hR t x)

def perpL (cv : CrdV A) (j : Bs.J) (t : Bs.Tup) (S : Submodule K (A.FL j t)) : Submodule K (A.FL j t) :=
  ⨅ x ∈ S, LinearMap.ker (cv.hL j t x)

end Defs

def PerpRatR : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) (cv : CrdV A),
    X.KFormR → X.JIsoR cv → ∀ t (S : Submodule K (A.FR t)),
      Submodule.span ℂ (X.jR t '' (perpR cv t S : Set (A.FR t))) =
        (Submodule.span ℂ (X.jR t '' (S : Set (A.FR t))))ᗮ

def PerpRatL : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) (cv : CrdV A),
    X.KFormL → X.JIsoL cv → ∀ j t (S : Submodule K (A.FL j t)),
      Submodule.span ℂ (X.jL j t '' (perpL cv j t S : Set (A.FL j t))) =
        (Submodule.span ℂ (X.jL j t '' (S : Set (A.FL j t))))ᗮ

def RatZOfTests : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) (cv : CrdV A),
    X.KFormR → X.KFormL → X.JIsoR cv → X.JIsoL cv → RowTest X → LiftTest X → X.RatZ

def RatMuOfRowTest : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool), RowTest X → X.H2 cr b → X.RATmu cr b

def RatThOfLiftTest : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool),
    LiftTestB X b → X.H5 cr b → X.KForm b → X.EWnorm b → 0 < X.nP b → X.RATth cr b

end Formalism.IndefR.Rat

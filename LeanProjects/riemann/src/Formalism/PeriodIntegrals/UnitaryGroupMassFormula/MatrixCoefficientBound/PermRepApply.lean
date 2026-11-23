import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic

open Finset Matrix

open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

section Defs

variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}

def placeOp (ψ : ∀ v, AddChar (Fq v) ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V) (v : ι) : V →ₗ[ℂ] V :=
  ∑ y : GL (Fin k) (Fq v), gam (ψ v) y • π (Pi.mulSingle v y)

def totOp (ψ : ∀ v, AddChar (Fq v) ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V) : V →ₗ[ℂ] V :=
  ∑ x : (∀ v, GL (Fin k) (Fq v)), gamProd ψ x • π x

end Defs

def permRep (G : Type) [Monoid G] (X : Type) [MulAction Gᵐᵒᵖ X] : Representation ℂ G (X → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (fun i => MulOpposite.op g • i)
  map_one' := by ext f i; simp [LinearMap.funLeft]
  map_mul' g h := by ext f i; simp [LinearMap.funLeft, mul_smul]

def GamInv : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (x : GL (Fin k) F),
    gam ψ₀ x⁻¹ = conj (gam ψ₀ x)

def MatrixEq : Prop :=
  ∀ (ι : Type) [Fintype ι] (Fq : ι → Type) [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] (k : ℕ)
    (ψ : ∀ v, AddChar (Fq v) ℂ) (X : Type) [Fintype X] [MulAction (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ X],
      (∀ (x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ) (j : X), x • j = j → x = 1) →
      ∀ d : X → X → (∀ v, GL (Fin k) (Fq v)),
        (∀ i j, (∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i) → MulOpposite.op (d i j) • j = i) →
        (Matrix.of fun i j =>
          if ∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i then conj (gamProd ψ (d i j)) else 0) =
            LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)) ∧
        (Matrix.of fun i j =>
          if ∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i then gamProd ψ (d i j) else 0) =
            (LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)))ᵀ

def TotHerm : Prop :=
  ∀ (ι : Type) [Fintype ι] (Fq : ι → Type) [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] (k : ℕ)
    (ψ : ∀ v, AddChar (Fq v) ℂ) (X : Type) [Fintype X] [MulAction (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ X],
    (LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X))).IsHermitian

def SpecPSD : Prop :=
  ∀ (X : Type) [Fintype X] (M : Matrix X X ℂ) (c : ℝ), M.IsHermitian →
    (∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → M *ᵥ w = μ • w → ∃ r : ℝ, μ = r ∧ 0 ≤ r ∧ r ≤ c) →
    M.PosSemidef ∧ ((c : ℂ) • (1 : Matrix X X ℂ) - M).PosSemidef

def PlaceBound : Prop :=
  ConvScalar → GenericRatio →
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 → 3 ≤ Fintype.card F →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (GL (Fin k) F) V) (W : Submodule ℂ V) (μ : ℂ), W ≠ ⊥ →
      (∀ g, ∀ w ∈ W, π g w ∈ W) → (∀ w ∈ W, repGam ψ₀ π w = μ • w) →
      ∃ c : ℝ, μ = gam ψ₀ (1 : GL (Fin k) F) * (c : ℂ) ∧ 0 ≤ c ∧ c ≤ 1 + 3 / (Fintype.card F : ℝ)

def JointEig : Prop :=
  ∀ (ι : Type) [Fintype ι] (Fq : ι → Type) [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] (k : ℕ)
    (ψ : ∀ v, AddChar (Fq v) ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V) (w : V) (μ : ℂ), w ≠ 0 → totOp ψ π w = μ • w →
    ∃ W : Submodule ℂ V, W ≠ ⊥ ∧ (∀ g, ∀ x ∈ W, π g x ∈ W) ∧ (∀ x ∈ W, totOp ψ π x = μ • x) ∧
      ∀ v, ∃ μv : ℂ, ∀ x ∈ W, placeOp ψ π v x = μv • x

def ProdFormula : Prop :=
  ∀ (ι : Type) [Fintype ι] (Fq : ι → Type) [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] (k : ℕ)
    (ψ : ∀ v, AddChar (Fq v) ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V) (μ : ι → ℂ) (w : V),
    (∀ v, placeOp ψ π v w = μ v • w) → totOp ψ π w = (∏ v, μ v) • w

def EigBound : Prop :=
  ConvScalar → GenericRatio →
  ∀ (ι : Type) [Fintype ι] (Fq : ι → Type) [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] (k : ℕ)
    (ψ : ∀ v, AddChar (Fq v) ℂ), (∀ v, ψ v ≠ 1) → (∀ v, 3 ≤ Fintype.card (Fq v)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V) (w : V) (μ : ℂ), w ≠ 0 → totOp ψ π w = μ • w →
      ∃ r : ℝ, μ = r ∧ 0 ≤ r ∧
        r ≤ (∏ v, (1 + 3 / (Fintype.card (Fq v) : ℝ))) * (gamProd ψ (1 : ∀ v, GL (Fin k) (Fq v))).re

end PI.GGMatBoundW

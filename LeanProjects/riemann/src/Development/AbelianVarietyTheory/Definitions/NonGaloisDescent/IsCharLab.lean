import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section

namespace GlobalTheory.GLp

open Polynomial GlobalTheory.GLq
open scoped Classical

variable (g : ℕ) [Fact g.Prime]

def inc (n : ℕ) : GL (Fin n) ℤ_[g] →* GL (Fin n) ℚ_[g] :=
  Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g])

def red (n : ℕ) : GL (Fin n) ℤ_[g] →* Gn g n := Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := g))

def lift (n : ℕ) (x : Gn g n) : GL (Fin n) ℚ_[g] := inc g n (Function.invFun (red g n) x)

variable {g} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def fixK1 (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : Submodule ℂ V :=
  ⨅ k : (red g n).ker, LinearMap.ker (π (inc g n k) - LinearMap.id)

def actK (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a : MonoidAlgebra ℂ (Gn g n)) : V →ₗ[ℂ] V :=
  ∑ x : Gn g n, a.coeff x • π (lift g n x)

def IsIrrRep {G : Type} [Group G] (π : Representation ℂ G V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ x, ∀ v ∈ W, π x v ∈ W) → W = ⊥ ∨ W = ⊤

def HasLab (L : LabelDatum g) (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (f : (ZMod g)[X]) : Prop :=
  ∃ v ∈ fixK1 π, actK π (eSerC L n f) v ≠ 0

def blk (a b n : ℕ) (x : Gn g a) (y : Gn g b) : Gn g n :=
  toG (fun i j : Fin n =>
    if (i : ℕ) < a ∧ (j : ℕ) < a then Formalism.MainNotions.ArithmeticCylinders.entN (x : Mt g a) i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then Formalism.MainNotions.ArithmeticCylinders.entN (y : Mt g b) (i - a) (j - a) else 0)

def IsParVec (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (v : V) : Prop :=
  v ∈ fixK1 π ∧
    (∀ u : Gn g n, InPar a (u : Mt g n) → tl a (u : Mt g n) = 1 → br a b (u : Mt g n) = 1 → π (lift g n u) v = v) ∧
    ∀ y : Gn g b, π (lift g n (blk a b n 1 y)) v = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • v

def actTop (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (e : MonoidAlgebra ℂ (Gn g a)) : V →ₗ[ℂ] V :=
  ∑ x : Gn g a, e.coeff x • π (lift g n (blk a b n x 1))

def IsCharLab (L : LabelDatum g) (χ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g) : Prop :=
  c ≠ 0 ∧ ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 →
    ((χ u : ℂˣ) : ℂ) = L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c)

def MapsToInd {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) : Prop :=
  ∃ Λ : V →ₗ[ℂ] W, Λ ≠ 0 ∧ ∀ (p : GL (Fin n) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
    (∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j = 0) →
    (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j) →
    (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin n) (Fin n) ℚ_[g]) (a + i) (a + j)) →
    ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
      σ x (Λ v)

end GlobalTheory.GLp

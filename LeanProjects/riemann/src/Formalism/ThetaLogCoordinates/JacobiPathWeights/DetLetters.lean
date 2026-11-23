import Mathlib

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

variable {ι ζ : Type*} {n : ℕ}

abbrev LVar (ι ζ : Type*) (n : ℕ) := (ι × Fin n) ⊕ ζ

def diagS (A : Type*) [CommRing A] (n : ℕ) (last : Bool) (e : ℤ) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial A) :=
  Matrix.diagonal fun a =>
    if (if last then a.val + 1 = n else a.val = 0) then LaurentPolynomial.T e else 1

def conjS {L : Type*} [CommRing L] (τ : Type*) (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (e : ℤ) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial (MvPolynomial τ L)) :=
  g.map (fun c => LaurentPolynomial.C (C c)) * diagS (MvPolynomial τ L) n last e *
    gi.map (fun c => LaurentPolynomial.C (C c))

def conjAct {k L : Type*} [CommRing k] [CommRing L] (φ : k →+* L) (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) :
    MvPolynomial (LVar ι ζ n) k →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L) :=
  eval₂Hom ((LaurentPolynomial.C).comp ((C).comp φ)) fun x =>
    match x with
    | Sum.inl (i, a) =>
      if i ∈ S then
        (if isVec i then
          Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b)))) (conjS _ g gi last 1) a
        else
          Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b))))
            (conjS _ g gi last (-1)).transpose a)
      else LaurentPolynomial.C (X (Sum.inl (i, a)))
    | Sum.inr z => LaurentPolynomial.C (X (Sum.inr z))

abbrev GenField (k : Type*) [Field k] (n : ℕ) := FractionRing (MvPolynomial (Fin n × Fin n) k)

def genMat (k : Type*) [Field k] (n : ℕ) : Matrix (Fin n) (Fin n) (GenField k n) :=
  Matrix.of fun a b => algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n) (X (a, b))

def genAct (k : Type*) [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool) :
    MvPolynomial (LVar ι ζ n) k →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) (GenField k n)) :=
  conjAct ((algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C) isVec S
    (genMat k n) (genMat k n)⁻¹ last

def valS {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : WithTop ℤ :=
  (genAct k isVec S true G).coeff.support.min

def lam1S {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : WithBot ℤ :=
  (genAct k isVec S false G).coeff.support.max

def detLetters (k : Type*) [CommRing k] (A : Fin n → ι) : MvPolynomial (LVar ι ζ n) k :=
  (Matrix.of fun l a => (X (Sum.inl (A l, a)) : MvPolynomial (LVar ι ζ n) k)).det

def degIn (U : Set ι) [DecidablePred (· ∈ U)] (e : LVar ι ζ n →₀ ℕ) : ℕ :=
  e.sum fun x d => match x with
    | Sum.inl (i, _) => if i ∈ U then d else 0
    | Sum.inr _ => 0

end Formalism.InvariantFactorPaths.GelfandTsetlinBases

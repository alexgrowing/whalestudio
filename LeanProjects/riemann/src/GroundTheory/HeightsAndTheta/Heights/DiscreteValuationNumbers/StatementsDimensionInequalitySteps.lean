import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

open Polynomial

def PolynomialPrimeOverZeroHeight.Statement : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] (Q : Ideal D[X]) [Q.IsPrime],
    Q.comap (C : D →+* D[X]) = ⊥ → Q.height ≤ 1

def QuotientHeightAddOne.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (I : Ideal R), I ≠ ⊥ →
    ∀ (P : Ideal (R ⧸ I)) [P.IsPrime], P.height + 1 ≤ (P.comap (Ideal.Quotient.mk I)).height

def PolynomialDimensionInequality.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (P : Ideal A[X]) [P.IsPrime],
    Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P) ≤
      Cardinal.ofENat (P.under A).height + 1

def DimensionInequalityOneGenerator.Statement : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (x : B), Algebra.adjoin A {x} = ⊤ → Function.Injective (algebraMap A B) →
    ∀ (P : Ideal B) [P.IsPrime],
      Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (B ⧸ P) ≤
        Cardinal.ofENat (P.under A).height + Algebra.trdeg A B

end GroundTheory.Heights₂.Heights.NumbersDVR

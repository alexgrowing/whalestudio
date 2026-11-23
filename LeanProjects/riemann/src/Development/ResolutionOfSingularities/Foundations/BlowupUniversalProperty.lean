import Mathlib

section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.Blowup

def IsLocallyGeneratedByNonZeroDivisor {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U.1)),
    x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ I.ideal U = Ideal.span {f}

def IsBlowupAlongIdealSheaf {X X' : Scheme.{u}} (π : X' ⟶ X) (I : X.IdealSheafData) : Prop :=
  IsLocallyGeneratedByNonZeroDivisor (I.comap π) ∧
    ∀ (W : Scheme.{u}) (g : W ⟶ X), IsLocallyGeneratedByNonZeroDivisor (I.comap g) →
      ∃! h : W ⟶ X', h ≫ π = g

end FunctorialResolution.Blowup

end

end

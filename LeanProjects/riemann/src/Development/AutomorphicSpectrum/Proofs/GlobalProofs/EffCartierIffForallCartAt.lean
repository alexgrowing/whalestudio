import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

def CartAt {X : Scheme.{0}} (J : X.IdealSheafData) (x : X) : Prop :=
  ∃ (U : X.affineOpens) (f : Γ(X, U.1)), x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ J.ideal U = Ideal.span {f}

theorem effCartier_iff_forall_cartAt {X : Scheme.{0}} (J : X.IdealSheafData) :
    FinalTheorems.EffCartier J ↔ ∀ x, CartAt J x := Iff.rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

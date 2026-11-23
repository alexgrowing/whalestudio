import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsIntegralPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

noncomputable section

def ClosedPointOfGenericFibre.Hyp (R : Type) [CommRing R] (M : Ideal R) (g : R) : Prop :=
  M.IsMaximal ∧ g ≠ 0

def ClosedPointOfGenericFibre.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R]
    [Module.Flat (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (M : Ideal R) (g : R),
    ClosedPointOfGenericFibre.Hyp R M g →
    ∃ Q : Ideal R, Q.IsPrime ∧ Q ≤ M ∧ Q.comap (algebraMap (𝓞 F) R) = ⊥ ∧ g ∉ Q ∧
      Algebra.IsAlgebraic (𝓞 F) (R ⧸ Q)

def ClosedPointOfGenericFibre.exampleIdeal : Ideal (Polynomial (𝓞 ℚ)) :=
  RingHom.ker ((Ideal.Quotient.mk placeTwo.asIdeal).comp (Polynomial.evalRingHom 0))

end

end GroundTheory.Heights₂.Heights.FourB

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatNormalFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def FormalFibresRegular.Statement : Prop :=
  ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A], Algebra.FiniteType k A →
    ∀ (m : Ideal A), m.IsMaximal → ∀ (P : Ideal (AdicCompletion m A)) [P.IsPrime],
      IsRegularLocalRing (primeFibreLocalRing A P)

noncomputable def polyOriginIdeal : Ideal (MvPolynomial (Fin 1) ℂ) :=
  RingHom.ker (MvPolynomial.eval (0 : Fin 1 → ℂ))

theorem polyOriginIdeal_isMaximal : polyOriginIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun z => ⟨MvPolynomial.C z, by simp⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

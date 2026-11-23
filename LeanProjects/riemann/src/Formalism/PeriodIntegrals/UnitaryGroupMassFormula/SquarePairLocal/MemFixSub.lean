import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOfSteps

noncomputable section
open NumberField

namespace PI.SqPairLocal

def fixSub {R : Type} [CommRing R] (σ : R ≃+* R) : Subring R :=
  (σ : R →+* R).eqLocus (RingHom.id R)

theorem mem_fixSub {R : Type} [CommRing R] (σ : R ≃+* R) (x : R) : x ∈ fixSub σ ↔ σ x = x :=
  Iff.rfl

def FixedDVR : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    [Finite (IsLocalRing.ResidueField R)] (σ : R ≃+* R), (∀ x, σ (σ x) = x) →
    ∀ ϖ : R, Irreducible ϖ → σ ϖ = ϖ →
      ∃ (_ : IsDiscreteValuationRing (fixSub σ)) (_ : HenselianLocalRing (fixSub σ))
        (_ : Finite (IsLocalRing.ResidueField (fixSub σ))),
        ∀ h : ϖ ∈ fixSub σ, Irreducible (⟨ϖ, h⟩ : fixSub σ)

def RealUnif : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (cj E) = Q →
      ∃ ϖ : 𝓞 E, cj E ϖ = ϖ ∧ ϖ ∈ Q ∧ ϖ ∉ Q ^ 2

end PI.SqPairLocal

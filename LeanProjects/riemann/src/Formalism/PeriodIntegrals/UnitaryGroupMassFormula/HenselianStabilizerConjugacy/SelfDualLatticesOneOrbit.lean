import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.LocEExistsDelta

noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

def SelfDualLatticesOneOrbit : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (Λ₁ Λ₂ : Submodule M.L.O V),
      IsSelfDual H Λ₁ → IsSelfDual H Λ₂ →
      ∃ g : V ≃ₗ[E] V, IsUnitary H g ∧ img g Λ₁ = Λ₂

end PI.SelfDualHermitianLattices

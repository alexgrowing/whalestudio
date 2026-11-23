import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def GramDetermines.Statement (h : HermitianForm F E W) : Prop :=
  ∀ (n : ℕ) (e e' : Fin n → W), IsLattice E (AddSubgroup.closure (Set.range e)) →
    IsLattice E (AddSubgroup.closure (Set.range e')) →
    (∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) →
    ∃ γ : h.unitaryGroup, ∀ a, (γ : W ≃ₗ[E] W) (e a) = e' a

end

end GroundTheory.Heights₂.Heights.FiniteCovolume

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.TrivBundleIsTwistedForms
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def LineFibreBlocks.Statement : Prop :=
  ∀ (F : Type) [Field F] (K₀ : Type) [Fintype K₀] (ι₀ : K₀ → Type) [∀ k, Fintype (ι₀ k)] (k₀ : K₀)
    (Q : Ideal (MRingOver F ι₀)) (J : IFamily F ι₀),
    (∀ k, k = k₀) → IsProjVarF Q 1 →
    (∃ S : Set (MRingOver F ι₀), (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ Q = Ideal.span S) →
    IsFieldIntersection J → ∀ m : K₀ → ℤ, J Q 1 ![m] = m k₀

end GroundTheory.Heights₂.Heights.Inter

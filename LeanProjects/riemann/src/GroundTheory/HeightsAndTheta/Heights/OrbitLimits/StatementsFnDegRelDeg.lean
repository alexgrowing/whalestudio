import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

def FnDegRelDeg.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
    (ι : K → Type) [∀ k, Fintype (ι k)] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hκv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v)
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (i' : ∀ k', ι' k'),
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsChart P' i' →
      haveI := hP'.isPrime
      ReciprocityTheory.ChartRestriction.G.AI.I1.fnDeg v P' i' = relDeg ⟨κ, hκv.1⟩ P'

section Inhabitants

def firstFactor : (Σ _ : Unit, Fin 2) → (Σ _ : Fin 2, Fin 2) := fun p => ⟨0, p.2⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Targets

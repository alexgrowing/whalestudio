import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def ChartRankAdjoin.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ Φ' : Type) [Field Φ] [Field Φ'] [Algebra Φ Φ']
    (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k),
    (∀ k, z ⟨k, j k⟩ ≠ 0) → IsMultiHomogIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) →
      ptDeg (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) j =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range fun q : Σ k, ι k => z q / z ⟨q.1, j q.1⟩))

section Inhabitants

def genericPointProjLine : (Σ _ : Unit, Fin 2) → FractionRing (MvPolynomial (Σ _ : Unit, Fin 2) ℚ) :=
  fun q => algebraMap (MvPolynomial (Σ _ : Unit, Fin 2) ℚ) _ (X q)

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter

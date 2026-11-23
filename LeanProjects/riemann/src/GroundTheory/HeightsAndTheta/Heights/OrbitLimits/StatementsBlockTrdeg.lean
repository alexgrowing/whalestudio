import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
    (L : Type) [Field L] [Algebra ℚ L] (φ : MRing ι' →+* L),
    IsBlockMap κ v → IsMultiProjPrime P' → RingHom.ker φ = P' →
      Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p)))) +
          ((Fintype.card K' - Fintype.card K : ℕ) : Cardinal) ≤
        Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range fun q : Σ k', ι' k' ↦ φ (X q)))

section Examples

abbrev pointBlocks : Unit → Type := fun _ ↦ Unit

def genericPairMap :
    MRing (Sum.elim pointBlocks pointBlocks) →+*
      FractionRing (MvPolynomial (Σ k : Unit ⊕ Unit, Sum.elim pointBlocks pointBlocks k) ℚ) :=
  (algebraMap (MvPolynomial (Σ k : Unit ⊕ Unit, Sum.elim pointBlocks pointBlocks k) ℚ) _).comp
    (MvPolynomial.map (Int.castRingHom ℚ))

end Examples

end GroundTheory.Heights₂.Heights

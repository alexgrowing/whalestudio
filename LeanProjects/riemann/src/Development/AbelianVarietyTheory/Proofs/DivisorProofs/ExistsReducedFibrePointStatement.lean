import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReducedFibrePoint
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduced_fibre_point : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (z : Z),
  z ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) → ∃ y : reducedSpecialFibre f, reducedSpecialι f y = z := by
  first | exact @GlobalTheory.exists_reducedSpecialFibre_of_not_mem_basicOpen | exact GlobalTheory.exists_reducedSpecialFibre_of_not_mem_basicOpen | (intros; apply GlobalTheory.exists_reducedSpecialFibre_of_not_mem_basicOpen <;> assumption)

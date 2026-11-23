import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSchemeSpecialFibreNonempty
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_scheme_special_fibre_nonempty : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)), Flat f → Nonempty (specialFibre f) →
  genericPoint Z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ∧ ∃ z : Z, z ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) := by
  first | exact @GlobalTheory.FlatDVRFibre.genericPoint_mem_and_exists_not_mem | exact GlobalTheory.FlatDVRFibre.genericPoint_mem_and_exists_not_mem | (intros; apply GlobalTheory.FlatDVRFibre.genericPoint_mem_and_exists_not_mem <;> assumption)

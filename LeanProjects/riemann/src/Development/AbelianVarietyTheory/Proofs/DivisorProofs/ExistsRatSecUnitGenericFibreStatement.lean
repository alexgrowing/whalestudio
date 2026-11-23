import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatSecUnitGenericFibre
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratSec_unit_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)) (D : LB Z), Flat f → D.IsLB →
  ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
  ∃ τ : D.ι → Z.functionFieldˣ, IsRatSec D τ ∧
    (∀ (i : D.ι) (z : Z), z ∈ D.U i → z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
      UnitAt z (τ i : Z.functionField)) ∧
    ∀ (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen),
      (∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
        fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n =
          (τ i : Z.functionField) ^ M) →
      PowEq f ϖ hϖ D sig M n gen := by
  first | exact @GlobalTheory.GenericRatSec.exists_ratSec | exact GlobalTheory.GenericRatSec.exists_ratSec | (intros; apply GlobalTheory.GenericRatSec.exists_ratSec <;> assumption)

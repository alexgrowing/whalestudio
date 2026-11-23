import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSectionExtendsOverFibre
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_section_extends_over_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D → genericPoint Z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  IsField Γ(reducedSpecialFibre f, ⊤) →
  (∀ (φ : Z.functionField) (x : Z),
    (∀ z : Z, z ⤳ x → IsDiscreteValuationRing (Z.presheaf.stalk z) → RegAt z φ) → RegAt x φ) →
  ∀ τ : D.ι → Z.functionFieldˣ, IsRatSec D τ →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) → UnitAt z (τ i : Z.functionField)) →
  ∀ (M : ℕ) (n : ℤ) (x₀ : Z), 1 ≤ M → x₀ ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
  (∀ (i : D.ι) (z : Z), z ∈ D.U i → IsDiscreteValuationRing (Z.presheaf.stalk z) →
    RegAt z (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  (∀ i : D.ι, x₀ ∈ D.U i → UnitAt x₀ (fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n * ((τ i : Z.functionField) ^ M)⁻¹)) →
  ∃ gen : (lbPow D M).Gen, gen.IsGen ∧
    ∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
      fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n = (τ i : Z.functionField) ^ M := by
  first | exact @GlobalTheory.PropZCore.gen_of_exponent | exact GlobalTheory.PropZCore.gen_of_exponent | (intros; apply GlobalTheory.PropZCore.gen_of_exponent <;> assumption)

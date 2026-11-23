import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareEquivOfBaseChangeFieldStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem wedgeO_descends_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → WedgeO (OAff B.hom) → WedgeO (OAff A.hom) := by
  intro K L _ _ _ A _ B _ φ h hA hB
  have hp : IsProper A.hom := hA.proper
  obtain ⟨⟨e₁, he₁⟩, e₂, he₂⟩ :=
    GlobalTheory.T.structure_cohomology_flat_base_change K L A.left B.left A.hom B.hom φ h.1 inferInstance inferInstance
  refine GlobalTheory.T.exteriorSquare_equiv_of_baseChange_field K L _ _ _ _ (cup (OAff A.hom)) (cup (OAff B.hom)) e₁ e₂ (fun a b ↦ ?_) hB
  rw [he₁, he₁, he₂]
  exact (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.2.1 K L A.left B.left A.hom B.hom _ φ h.1.w).1 a b

end GlobalTheory.AbCoh

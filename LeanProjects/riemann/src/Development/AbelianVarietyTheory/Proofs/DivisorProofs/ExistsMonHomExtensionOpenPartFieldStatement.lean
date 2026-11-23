import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomExtensionOpenPartField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monHom_extension_openPart_field : ∀ (K : Type) [Field K] (H G V : Over (Sp K)) [GrpObj H] [GrpObj G], GlobalTheory.SS.SmConn H → GlobalTheory.SS.SmConn G → ∀ (j : V ⟶ H) (f : V ⟶ G), IsOpenImmersion j.left → Nonempty V.left → (∀ (Z : Over (Sp K)) (u₁ u₂ u₃ : Z ⟶ V), (u₁ ≫ j) * (u₂ ≫ j) = u₃ ≫ j → (u₁ ≫ f) * (u₂ ≫ f) = u₃ ≫ f) → ∃ F : H ⟶ G, IsMonHom F ∧ j ≫ F = f := by
  first | exact @GlobalTheory.GenericHomField.exists_monHom_extension_of_field | exact GlobalTheory.GenericHomField.exists_monHom_extension_of_field | (intros; apply GlobalTheory.GenericHomField.exists_monHom_extension_of_field <;> assumption)

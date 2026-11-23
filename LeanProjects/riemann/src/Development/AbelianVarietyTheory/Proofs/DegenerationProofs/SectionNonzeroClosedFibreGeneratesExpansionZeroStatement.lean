import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionNonzeroClosedFibreGeneratesExpansionZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_nonzero_closedFibre_generates_expansion_zero : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : H0 U.LG.L 1, (∃ g, G.hom g = closedPoint V ∧ g ∈ nonzeroLocus σ) → (∀ s : H0 U.LG.L 1, ∃ b : V, SecIsMul G.hom b s σ) ∧ ∀ σ' : U.SecGF F 1, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) → ∃ ϑ, U.ExpandsG F 1 σ' ϑ ∧ Prim D Q v ϑ := by
  first | exact @GlobalTheory.Ex.PrimitiveExpansion.main | exact GlobalTheory.Ex.PrimitiveExpansion.main | (intros; apply GlobalTheory.Ex.PrimitiveExpansion.main <;> assumption)

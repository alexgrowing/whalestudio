import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupScheme
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_subgroup_scheme : ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A), IsFinFlatSub A B h → ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.SubGrp.grpObj_of_isFinFlatSub | exact GlobalTheory.CompanionTheory.Ar.GR.SubGrp.grpObj_of_isFinFlatSub | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.SubGrp.grpObj_of_isFinFlatSub <;> assumption)

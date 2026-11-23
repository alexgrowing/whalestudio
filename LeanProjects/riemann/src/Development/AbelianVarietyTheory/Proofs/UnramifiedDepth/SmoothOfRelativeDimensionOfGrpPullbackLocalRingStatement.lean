import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SmoothOfRelativeDimensionOfGrpPullbackLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_grpPullback_localRing : ∀ (R' O : Type) [CommRing R'] [IsLocalRing R'] [CommRing O] [Nontrivial O] (π : R' →+* O) (G : Over (Spec (CommRingCat.of R'))) [GrpObj G] (G' : Over (Spec (CommRingCat.of O))) [GrpObj G'] (ψ : G'.left ⟶ G.left) (g : ℕ), IsAbelianScheme G → Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom π)) ψ → SmoothOfRelativeDimension g G'.hom → SmoothOfRelativeDimension g G.hom := by
  first | exact @GlobalTheory.LiftDim.smoothOfRelativeDimension_of_isGrpPullback | exact GlobalTheory.LiftDim.smoothOfRelativeDimension_of_isGrpPullback | (intros; apply GlobalTheory.LiftDim.smoothOfRelativeDimension_of_isGrpPullback <;> assumption)

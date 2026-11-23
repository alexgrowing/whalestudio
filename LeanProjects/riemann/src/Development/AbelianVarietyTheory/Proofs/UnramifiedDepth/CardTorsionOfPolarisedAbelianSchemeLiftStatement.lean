import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CardTorsionOfPolarisedAbelianSchemeLift
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
theorem _root_.GlobalTheory.T.card_torsion_of_polarisedAbelianScheme_lift : ∀ (R O C : Type) [CommRing R] [CommRing O] [Field C] [IsAlgClosed C] [Algebra R O] [Algebra O C] [Algebra R C] [IsScalarTower R O C] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : Out.PolAV (Geo.Tor.Sp O)) (ψ : P.A.left ⟶ G.left), Geo.Tor.IsGrpPullback P.A G (Spec.map (CommRingCat.ofHom (algebraMap R O))) ψ → ∀ n : ℕ, (n : C) ≠ 0 → Nat.card {z : sp (R₀ := R) C ⟶ G // z ^ n = 1} = n ^ (2 * P.g) := by
  first | exact @GlobalTheory.ChF.card_torsion_of_isGrpPullback | exact GlobalTheory.ChF.card_torsion_of_isGrpPullback | (intros; apply GlobalTheory.ChF.card_torsion_of_isGrpPullback <;> assumption)

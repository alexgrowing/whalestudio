import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopologicalKrullDimLeOfFiniteCommonZeros
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.topologicalKrullDim_le_of_finite_common_zeros : Out.Laws → ∀ (K : Type) [Field K] (x : KeyIn K) (n r : ℕ) (s : Fin r → RR x n) (W : Set x.P.A.left), 1 ≤ n → IsClosed W → W.Nonempty → {y ∈ W | ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → topologicalKrullDim W ≤ r := by
  first | exact @GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros | exact GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros | (intros; apply GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros <;> assumption)

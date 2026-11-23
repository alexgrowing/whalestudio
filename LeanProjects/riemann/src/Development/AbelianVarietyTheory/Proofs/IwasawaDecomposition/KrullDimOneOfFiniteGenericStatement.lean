import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArithmeticVarietyDimZeroFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krullDim_one_of_finite_generic : ∀ (Z' Z : Scheme.{0}) [IsIntegral Z'] [IsIntegral Z] [IsNoetherian Z] (f : Z' ⟶ Z) [IsProper f], topologicalKrullDim Z = 1 → f (genericPoint Z') = genericPoint Z → 0 < f.residueDegree (genericPoint Z') → topologicalKrullDim Z' = 1 := by
  first | exact @GlobalTheory.ProperCover.dim_eq_one | exact GlobalTheory.ProperCover.dim_eq_one | (intros; apply GlobalTheory.ProperCover.dim_eq_one <;> assumption)

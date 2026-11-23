import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdPullbackMulResidueDegreeCodimOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_ord_pullback_mul_residueDegree_codim_one : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (π : Y ⟶ X) (hη : π (genericPoint Y) ⤳ genericPoint X) (z : X), Order.coheight z = 1 → (∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U)) → ∀ f : X.functionField, f ≠ 0 → ∑ᶠ (w : Y) (_ : π w = z), Scheme.ord (TrueGeo.SmallSec.fnMap π hη f) w * (π.residueDegree w : ℤ) = (π.residueDegree (genericPoint Y) : ℤ) * Scheme.ord f z := by
  first | exact @GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree | exact GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree | (intros; apply GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree <;> assumption)

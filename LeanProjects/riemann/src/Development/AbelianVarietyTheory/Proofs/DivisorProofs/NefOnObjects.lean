import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MbIsModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedModelDominantCurveRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefInducedBundleRestrictionToCurvesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical

namespace GlobalTheory.NefAtObj

theorem nefAt_onObj : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → OnObj fun _ _ A _ _ _ => NefAt A := by
  intro hX hP hH D O hc hf A T H h B hB u s hu hs hdom hnef hsemi c
  obtain ⟨M, L, k, cf, hI⟩ := GlobalTheory.ApproxModel.mb_isModel hP hH D O hc A T H h B hB u s hu hs hdom hsemi c
  refine ⟨M, L, k, cf, hI, ?_⟩
  refine GlobalTheory.ArInt.nefFib_of_primeField _ _ _ L fun Z i _ _ q _ _ hZ => ?_
  by_cases hq : q ∈ FlagAr.setB O.Y B
  · exact GlobalTheory.T.induced_model_dominant_curve_restriction hP hH D O hc hf A T H h B hB u s hu hs hdom c M L k cf hI Z i q hq hZ
  · exact GlobalTheory.T.nef_induced_bundle_restriction_to_curves hX hP hH D O hc A T H h B hB u s hu hs hdom hnef c M L k cf hI Z i q hq hZ

end GlobalTheory.NefAtObj

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_of_integral_valuation_bound : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (U : V.X.Opens) (f : V.X.functionField), (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (z ≫ V.j) f) ≤ 1) → ∀ x ∈ U, RegAt x f := by
  first | exact @GlobalTheory.Mean4O.Cover.RegCrit.regAt_of_integral_values | exact GlobalTheory.Mean4O.Cover.RegCrit.regAt_of_integral_values | (intros; apply GlobalTheory.Mean4O.Cover.RegCrit.regAt_of_integral_values <;> assumption)

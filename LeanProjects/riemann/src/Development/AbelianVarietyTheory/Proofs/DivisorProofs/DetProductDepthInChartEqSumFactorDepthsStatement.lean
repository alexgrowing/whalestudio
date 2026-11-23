import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetProductDepthInChartEqSumFactorDepths
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detProductDepthInChart_eq_sum_factorDepths : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), nuProdC Ch X cx = ∑ f : Lt1 Dw, nuFacC Ch X f (cx f) := by
  first | exact @GlobalTheory.FactorDepthProd.nuProdC_eq_sum | exact GlobalTheory.FactorDepthProd.nuProdC_eq_sum | (intros; apply GlobalTheory.FactorDepthProd.nuProdC_eq_sum <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthEqChartValueAndSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFactorDepth_eq_chart_value_and_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), (∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k) ∧ ∀ cx : Lt1 Dw → ℕ, nuProd p y cx = nuP p y cx := by
  first | exact @GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP | exact GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP | (intros; apply GlobalTheory.FactorDepth.nuFac_eq_nuFacC_and_nuProd_eq_nuP <;> assumption)

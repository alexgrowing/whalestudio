import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartIndependentClosedFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetProductDepthInChartEqSumFactorDepthsStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

namespace GlobalTheory.FactorDepth

theorem nuFac_eq_nuFacC_and_nuProd_eq_nuP :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
      ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
        (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
        (∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k) ∧
          ∀ cx : Lt1 Dw → ℕ, nuProd p y cx = nuP p y cx := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X
  have hc : ∀ (Ch' : IntegralChartA3 Xo c T io y) (X' : ValExt T p) (f : Lt1 Dw) (k : ℕ),
      nuFacC Ch' X' f k = nuFacC Ch X f k := fun Ch' X' f k =>
    (GlobalTheory.T.detFactorDepthInChart_chart_independent E H Dw l Xo c p T io y Ch' Ch X' f k).trans
      (GlobalTheory.T.detFactorDepthInChart_independent_closedField E H Dw l Xo c p T io y Ch X' X f k)
  have h1 : ∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k := fun f k =>
    le_antisymm (nuFac_le Ch X f k) (le_nuFac fun Ch' X' => (hc Ch' X' f k).ge)
  refine ⟨h1, fun cx => ?_⟩
  have h2 : ∀ (Ch' : IntegralChartA3 Xo c T io y) (X' : ValExt T p), nuProdC Ch' X' cx = nuP p y cx := by
    intro Ch' X'
    rw [GlobalTheory.T.detProductDepthInChart_eq_sum_factorDepths E H Dw l Xo c p T io y Ch' X' cx, nuP]
    exact Finset.sum_congr rfl fun f _ => (hc Ch' X' f (cx f)).trans (h1 f (cx f)).symm
  exact le_antisymm (iInf_le_of_le Ch (iInf_le_of_le X (h2 Ch X).le))
    (le_iInf₂ fun Ch' X' => (h2 Ch' X').ge)

end GlobalTheory.FactorDepth

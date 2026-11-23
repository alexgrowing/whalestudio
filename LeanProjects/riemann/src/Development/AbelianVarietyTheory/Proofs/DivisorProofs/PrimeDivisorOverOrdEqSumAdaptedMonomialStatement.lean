import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverOrdEqSumAdaptedMonomial
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeDivisorOver_ord_eq_sum_adaptedMonomial : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [GlobalTheory.IsNormalScheme Y] {q : Y ⟶ Sp k} (E : DivOver q) (y : Y), E.Through y →
    ∀ {ι : Type} [Fintype ι] (w : ι → Y) (u : ι → Y.functionFieldˣ), Function.Injective w →
    (∀ j, w j ⤳ y) → (∀ j, Order.coheight (w j) = 1) →
    (∀ j, Scheme.ord (u j : Y.functionField) (w j) = 1) →
    (∀ j v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0) →
    ∀ φ : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j, v ≠ w j) → Scheme.ord (φ : Y.functionField) v = 0) →
      E.ord φ = ∑ j, Scheme.ord (φ : Y.functionField) (w j) * E.ord (u j) := by
  first | exact @GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial | exact GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial | (intros; apply GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial <;> assumption)

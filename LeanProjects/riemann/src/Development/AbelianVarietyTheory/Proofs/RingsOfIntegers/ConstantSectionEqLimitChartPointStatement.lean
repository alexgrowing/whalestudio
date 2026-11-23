import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantSectionEqLimitChartPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantSection_eq_limitChart_point : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (G : Over (Sp V)) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (X : limO V d 1 ⟶ G), IsLimit x X → ∀ (α : Fin d → V) (hα : Small α) (aV : Sp V ⟶ G.left), (∀ m : ℕ, ∃ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] V ⧸ maximalIdeal V ^ (m + 1), (∀ p, ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (α p.2)) ∧ spMap (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))) ≫ aV = spMap (ψ : Jet V (Fin 1 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (x m).left) → ∀ n : ℕ, (ptOf X (Sm.const B α hα : Sm B n)).left = spMap (algebraMap V (PS V n d)) ≫ aV := by
  first | exact @GlobalTheory.TransUnit.ptOf_const_left | exact GlobalTheory.TransUnit.ptOf_const_left | (intros; apply GlobalTheory.TransUnit.ptOf_const_left <;> assumption)

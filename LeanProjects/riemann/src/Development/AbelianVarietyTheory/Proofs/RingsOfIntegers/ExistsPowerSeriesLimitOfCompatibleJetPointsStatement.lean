import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowerSeriesLimitOfCompatibleJetPoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_limit_of_compatible_jetPoints : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G), (∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m) → ∃ X : limO V d 1 ⟶ G, IsLimit x X := by
  first | exact @GlobalTheory.TransUnit.LimEx.exists_isLimit | exact GlobalTheory.TransUnit.LimEx.exists_isLimit | (intros; apply GlobalTheory.TransUnit.LimEx.exists_isLimit <;> assumption)

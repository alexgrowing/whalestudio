import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructure
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_rational_over_finite_extension_level_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ), 0 < M → (∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ AllRat Xo (spMap (algebraMap K L) ≫ x) M) ∧ (AllRat Xo x M → (∀ (L : Type) [Field L] (ψ : K →+* L), AllRat Xo (spMap ψ ≫ x) M) ∧ ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧ ∀ w : (ptO Xo x ⟶ Xo.univ.t.G), w ^ M = 1 → ∃ a, ev a = w) := by
  first | exact @GlobalTheory.torsion_rational_over_finite_extension | exact GlobalTheory.torsion_rational_over_finite_extension | (intros; apply GlobalTheory.torsion_rational_over_finite_extension <;> assumption)

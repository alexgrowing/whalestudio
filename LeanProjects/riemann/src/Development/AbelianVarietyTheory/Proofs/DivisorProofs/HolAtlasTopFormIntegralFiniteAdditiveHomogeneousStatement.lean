import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    (∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, IsFiniteMeasure (A.part α ε)) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), A.IsForm α → A.IsForm β → (∀ ε : ℤˣ, Integrable g (A.part α ε)) → (∀ ε : ℤˣ, Integrable g (A.part β ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part (α + β) ε)) ∧ wInt A g (α + β) = wInt A g α + wInt A g β) ∧
    (∀ (g : M → ℝ) (t : ℝ) (α : A.Fld), A.IsForm α → wInt A g ((t : ℂ) • α) = t * wInt A g α) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), (∀ x, dens (α x) = dens (β x)) → wInt A g α = wInt A g β) := by
  first | exact @GlobalTheory.LineForm.wInt_props | exact GlobalTheory.LineForm.wInt_props | (intros; apply GlobalTheory.LineForm.wInt_props <;> assumption)

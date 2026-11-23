import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeneratorRatioUnitExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_ratio_unit_exists : ∀ (X Y F : Scheme.{0}) (L : LB X) (M : LB Y) (f : F ⟶ X) (g : F ⟶ Y), L.IsLB → M.IsLB → ∀ (w : LB.Iso (L.pull f) (M.pull g)), w.IsGen → ∀ (Y' : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y' ⟶ F)) (φL : K → (Y' ⟶ X)) (φM : K → (Y' ⟶ Y)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φL ε)) (b : LB.Gen (LB.LinComb M φM ε)), (∀ i, φ i ≫ f = φL i) → (∀ i, φ i ≫ g = φM i) → c.IsGen → b.IsGen → ∃ u : Γ(Y', ⊤)ˣ, Tr w φ φL φM ε c b u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.exists_ratio_iso | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.exists_ratio_iso | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.exists_ratio_iso <;> assumption)

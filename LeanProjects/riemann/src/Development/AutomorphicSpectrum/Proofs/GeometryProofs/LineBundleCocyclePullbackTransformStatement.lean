import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleCocyclePullbackTransform
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_cocycle_pullback_transform : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (a b : Y ⟶ X), (∀ y, a y = b y) → ∀ (t : ∀ j, Γ(Y, b ⁻¹ᵁ L.U j)ˣ), (∀ (j j' : L.ι) (h : b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')), res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j from fun _ hy => hy.1) (t j) = Units.map (a.appLE _ _ h).hom.toMonoidHom (L.g j j') * (pullU b _ (L.g j j'))⁻¹ * res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j' from fun _ hy => hy.2) (t j')) → ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]), c.IsGen := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units | exact GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units <;> assumption)

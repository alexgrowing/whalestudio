import Development.WeilBound.CoreStatements.HodgeTatePoints.CdChart
import Development.WeilBound.CoreStatements.HodgeTatePoints.CdFrame
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd

noncomputable section
namespace PositivityTheory.HtPt.Cd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem germ_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ z : X0, ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X0) (d : ℕ), IsOpenImmersion j ∧ z ∈ Set.range j ∧ Nonempty (GermAt t j d) := by
  intro E _ _ _ H _ hs X0 t hp z
  obtain ⟨S, _, x0, d, G, A, tg, x, c, hj, hz, hc, ht, hb, hU⟩ := chart_affine E H X0 t z
  obtain ⟨e, ph1, ph2, sy, ad, hfr, htr, hfa, had⟩ := frame_affine E H X0 t S x0 d G A tg _ x c hc hU
  obtain ⟨hax, hr⟩ := FBIdAd.fbId E H X0 t hp hs S x0 _ G A _ tg _ x e ph1 ph2 sy ad hc hfr hfa had
  exact ⟨S, _, x0, d, hj, hz, ⟨⟨mkFB G A ph1 ph2 sy ad hax hr, x, e, tg, hc, ht, hb, hfr, htr, hfa⟩⟩⟩

end PositivityTheory.HtPt.Cd

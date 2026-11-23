import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjointRelationGeneratorCorr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_relation_generator_corr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x : Sp S ⟶ X) (d : ℕ) (g : GermAt t x d) (a : 𝓞 E) (wL : AdTy t a), wL.IsGen → AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (1 : jOG x d m 1 ⟶ t.G) (g.x m)).left) (LB.oneGen t.PP.L) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (g.x m) (1 : jOG x d m 1 ⟶ t.G)).left) (LB.oneGen t.PP.L) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis.adAxes | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis.adAxes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.WAxis.adAxes <;> assumption)

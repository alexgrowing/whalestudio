import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGermSubstitution
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_germ_substitution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ (m : ℕ) (a : 𝓞 E), (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g.B.A.act a p.2)).comp (sub1 Qs m) = (sub1 Qs m).comp (jetSubstP m fun p : Fin 1 × Fin d' => psTrunc m (gB.B.A.act a p.2)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.substitution_action_commutes | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.substitution_action_commutes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.substitution_action_commutes <;> assumption)

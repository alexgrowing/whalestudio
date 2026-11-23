import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductAdjoint
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_inner_product_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ t.G) (a : 𝓞 E) (c : ℂ), (∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L) → IsTanAt t.G z v → IsTanAt t.G z w → (HodgeIP t.G t.PP.L z (v ≫ t.act.act a) w c ↔ HodgeIP t.G t.PP.L z v (w ≫ t.act.act (H.bar a)) c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_act_adjoint | exact GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_act_adjoint | (intros; apply GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_act_adjoint <;> assumption)

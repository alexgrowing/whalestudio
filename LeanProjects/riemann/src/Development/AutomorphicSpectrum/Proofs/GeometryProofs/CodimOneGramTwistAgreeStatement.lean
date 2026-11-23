import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CodimOneGramTwistAgree
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.codim_one_gram_twist_agree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (t t' : SAB H X) (tp : SAB H (Spec (X.presheaf.stalk p.1))) (m : SABMap tp t (X.fromSpecStalk p.1)) (m' : SABMap (twistSAB tp g) t' (X.fromSpecStalk p.1)) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ V), (∀ e, ∃ v : Sp (DualNumber Ω) ⟶ tp.G.left, v ≫ m.φ = (M.pt e).left ∧ v ≫ m'.φ = (M'.pt e).left) → ∀ (z : Sp ℂ ⟶ X), centre z = p.1 → ∀ (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ), M.GramAt t.PP.L z b Γ ↔ M'.GramAt t'.PP.L z b Γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.codim_one_gram_twist_eq | exact GlobalTheory.CompanionTheory.Ar.codim_one_gram_twist_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.codim_one_gram_twist_eq <;> assumption)

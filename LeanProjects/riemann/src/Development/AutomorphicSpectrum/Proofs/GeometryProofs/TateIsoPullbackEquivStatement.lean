import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoPullbackEquiv
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_iso_pullback_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (k : Type) [Field k] (x' : Sp k ⟶ X') (x : Sp k ⟶ X), x = x' ≫ f → (∀ I : TateIsoAt D t x, ∃ I' : TateIsoAt D t' x', I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left) ∧ ∀ I' : TateIsoAt D t' x', ∃ I : TateIsoAt D t x, I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move | exact GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move <;> assumption)

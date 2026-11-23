import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.LineBundleSpreadsOut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_spreads_out : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp k) (p : X ⟶ Sp V) (φ : X ⟶ X₀), QuasiCompact p₀ → IsSeparated p₀ → IsPullback φ p p₀ (spMap (algebraMap k V)) → ∀ L : LB X, L.IsLB → ∃ R : Subalgebra k V, R.FG ∧ ∃ M : LB (pullback p₀ (spMap (algebraMap k R))), M.IsLB ∧ ∀ σ : X ⟶ pullback p₀ (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = φ → σ ≫ pullback.snd _ _ = p ≫ spMap R.val.toRingHom → LBIso L (M.pull σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.lb_descends_fg | exact GlobalTheory.CompanionTheory.Ar.Approx.lb_descends_fg | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.lb_descends_fg <;> assumption)

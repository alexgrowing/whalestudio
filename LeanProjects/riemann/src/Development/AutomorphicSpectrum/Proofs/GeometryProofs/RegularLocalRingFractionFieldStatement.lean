import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalRingFractionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_local_ring_fraction_field : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt | exact GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt <;> assumption)

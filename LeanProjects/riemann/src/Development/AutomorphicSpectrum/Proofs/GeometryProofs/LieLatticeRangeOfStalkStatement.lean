import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeRangeOfStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_range_of_stalk : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (h : IsCptGen ξ) (G : Over X) [GrpObj G] (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (Ep : Type) [AddCommGroup Ep] [Module (regAt ξ p) Ep] (Mp : LieModel G (regPt h p) Ep) (j : Ep →ₗ[regAt ξ p] E), (∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left) → (M.lat p : Set E) = Set.range j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range | exact GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range <;> assumption)

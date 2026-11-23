import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TorusPic

theorem triv_of_isLB_splitTorus : ∀ (A : Type) [CommRing A], IsField A → ∀ (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : LB (splitTorus (Sp A) X).left), N.IsLB → Triv N := by
  intro A _ hA X _ _ _ N hN
  letI := hA.toField
  have : IsAffine (splitTorus (Sp A) X).left := by
    have := Diag.isAffineHom_hom (Sp A) X
    exact isAffine_of_isAffineHom (splitTorus (Sp A) X).hom
  have := GlobalTheory.SS.LiftTorus.subsingleton_pic_torus A X
  exact GlobalTheory.LB.exists_isGen_of_subsingleton_pic_top hN

end GlobalTheory.TorusPic

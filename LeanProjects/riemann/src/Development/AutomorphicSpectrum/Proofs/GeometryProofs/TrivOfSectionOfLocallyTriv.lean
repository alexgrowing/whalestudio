import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactors

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem triv_of_section_of_locally_triv : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X), e ≫ p = 𝟙 S → (∀ U : S.Opens, IsIso (p.app U)) → ∀ M : LB X, M.IsLB → GlobalTheory.AbLaw.Triv (M.pull e) → (∀ x : S, ∃ U : S.Opens, x ∈ U ∧ GlobalTheory.AbLaw.Triv (M.pull (p ⁻¹ᵁ U).ι)) → GlobalTheory.AbLaw.Triv M :=
  fun _ _ p e he hp _ hM h₀ loc =>
    GlobalTheory.CubeGlue.triv_of_locally_triv hM p e he (GlobalTheory.CubeGlue.surjective_restrict p hp) h₀ loc

end GlobalTheory.CompanionTheory.Ar.Approx

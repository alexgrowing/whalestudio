import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem pspace_noeth_and_pullback : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
    IsProper π → ∀ N : ℕ, IsNoetherian (PSpace R N) ∧ IsNoetherian (pullback (PSpace.str R N) π) := by
  intro R _ _ S π hπ N
  have hP : IsProper (PSpace.str R N) := isProper_str R N
  have h1 : IsNoetherian (PSpace R N) := by
    have : IsLocallyNoetherian (PSpace R N) := LocallyOfFiniteType.isLocallyNoetherian (PSpace.str R N)
    have : CompactSpace (PSpace R N) := QuasiCompact.compactSpace_of_compactSpace (PSpace.str R N)
    exact {}
  refine ⟨h1, ?_⟩
  haveI := hπ
  have : IsProper (pullback.fst (PSpace.str R N) π) := inferInstance
  haveI := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (PSpace.str R N) π)
  haveI := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (PSpace.str R N) π)
  exact {}

end GlobalTheory.Mum

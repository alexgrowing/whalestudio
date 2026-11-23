import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_odd_prime_isUnit_of_base :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  intro R _ _ _ _
  by_cases h3 : IsUnit ((3 : ℕ) : R)
  · exact ⟨3, Nat.prime_three, ⟨1, rfl⟩, h3⟩
  by_cases h5 : IsUnit ((5 : ℕ) : R)
  · exact ⟨5, by norm_num, ⟨2, rfl⟩, h5⟩
  exfalso
  have m3 : ((3 : ℕ) : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h3
  have m5 : ((5 : ℕ) : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h5
  have m2 : ((5 : ℕ) : R) - ((3 : ℕ) : R) ∈ maximalIdeal R := Ideal.sub_mem _ m5 m3
  have m1 : ((3 : ℕ) : R) - (((5 : ℕ) : R) - ((3 : ℕ) : R)) ∈ maximalIdeal R := Ideal.sub_mem _ m3 m2
  have e : ((3 : ℕ) : R) - (((5 : ℕ) : R) - ((3 : ℕ) : R)) = 1 := by push_cast; ring
  rw [e] at m1
  exact (mem_maximalIdeal _).1 m1 isUnit_one

end GlobalTheory

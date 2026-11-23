import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DominantProjDegree

theorem residueDegree_ne_zero_of_map_genericPoint : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X = D → topologicalKrullDim Y = D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 := by
  intro k _ X Y _ _ p q D hp hq hX hY π hπ hη
  obtain ⟨N, i, hi, hcomp⟩ := hp
  obtain ⟨M, j, hj, hcomp'⟩ := hq
  haveI : IsProper (PSpace.str k N) := isProper_str k N
  haveI : IsProper (PSpace.str k M) := isProper_str k M
  haveI : IsProper p := by rw [← hcomp]; infer_instance
  haveI : IsProper (π ≫ p) := by rw [hπ, ← hcomp']; infer_instance
  haveI : IsProper π := IsProper.of_comp π p
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  have hsurj : Surjective π := ⟨fun x => by
    have : genericPoint X ∈ Set.range π := ⟨_, hη⟩
    exact (genericPoint_specializes x).mem_closed hcl this⟩
  exact GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero k Y X p π D inferInstance inferInstance
    hsurj hY hX

end GlobalTheory.DominantProjDegree

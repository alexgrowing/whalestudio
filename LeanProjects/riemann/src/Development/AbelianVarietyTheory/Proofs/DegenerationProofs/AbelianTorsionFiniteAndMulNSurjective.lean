import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteFibrePoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem surjective_mulN_of_isAbelianScheme (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B]
    (hB : IsAbelianScheme B) (n : ℕ) (hn : (n : K) ≠ 0) : Surjective (mulN B n).left := by
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have hft : LocallyOfFiniteType B.hom := inferInstance
  have : Flat (mulN B n).left :=
    MulEtaleDvr.flat_mulN_field K B n (isUnit_iff_ne_zero.2 hn) hft
  have : IsProper ((mulN B n).left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper (mulN B n).left := IsProper.of_comp _ B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : LocallyOfFinitePresentation (mulN B n).left := inferInstance
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  have hc : IsClopen (Set.range (mulN B n).left) :=
    ⟨(mulN B n).left.isClosedMap.isClosed_range, (mulN B n).left.isOpenMap.isOpen_range⟩
  exact ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty _))⟩

theorem abelian_torsion_finite_and_mulN_surjective :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) :=
  ⟨AbTorsionFinite.finite_torsion,
    fun K _ _ B _ hB n hn => surjective_mulN_of_isAbelianScheme K B hB n hn⟩

end GlobalTheory

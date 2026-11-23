import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_ext_torsion_points_good_reduction : Laws → Laws2 → ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → abLocus G = Set.univ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T F], Function.Injective (algebraMap T F) → ∀ k : ℕ, IsUnit (k : T) → ∃ (T' : Subalgebra T F) (_ : IsDiscreteValuationRing T'), (∀ π : T, Irreducible π → Irreducible (algebraMap T T' π)) ∧ ∀ x : Over.mk (spMap (algebraMap T F)) ⟶ G, x ^ k = 1 → ∃ x' : Sp T' ⟶ G.left, spMap (T'.val.toRingHom) ≫ x' = x.left := by
  first | exact @GlobalTheory.exists_unramified_torsion_points | exact GlobalTheory.exists_unramified_torsion_points | (intros; apply GlobalTheory.exists_unramified_torsion_points <;> assumption)

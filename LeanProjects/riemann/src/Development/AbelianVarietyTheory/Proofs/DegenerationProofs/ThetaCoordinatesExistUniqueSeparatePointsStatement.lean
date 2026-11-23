import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCoordinates_exist_unique_separate_points : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (s : Sp K ⟶ S) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (Ix : Type) (x : Ix → (Over.mk s ⟶ P.A)), (∀ i, x i ^ m ^ 2 = 1) → (∀ z, ∃ v : Ix → K, IsCoordPt P m x z fun i => fnOf (v i)) ∧ (∀ z (v v' : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → ((IsCoordPt P m x z fun i => fnOf (v' i)) ↔ ∃ c : Kˣ, v' = (c : K) • v)) ∧ (∀ v : Ix → K, (IsThetaPt P m x fun i => fnOf (v i)) ↔ IsCoordPt P m x 1 fun i => fnOf (v i)) ∧ (3 ≤ m → (∀ y : Over.mk s ⟶ P.A, y ^ m ^ 2 = 1 → ∃ i, x i = y) → ∀ z z' (v : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → (IsCoordPt P m x z' fun i => fnOf (v i)) → z = z' ∧ v ≠ 0) := by
  first | exact @GlobalTheory.CoordSep.coord_exists_unique_separate | exact GlobalTheory.CoordSep.coord_exists_unique_separate | (intros; apply GlobalTheory.CoordSep.coord_exists_unique_separate <;> assumption)

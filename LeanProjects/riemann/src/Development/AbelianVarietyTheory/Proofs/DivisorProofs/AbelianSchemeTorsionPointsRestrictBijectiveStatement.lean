import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointsRestrictBijective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateCondCongr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → ∀ (n : ℕ), 0 < n → IsUnit (n : Γ(S, ⊤)) →
    ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (t : Sp R ⟶ S)
    (K : Type) [Field K] (φ : R →+* K),
    (∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 →
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g =
        (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ h → g = h) ∧
    ∀ x : Over.mk (spMap φ ≫ t) ⟶ A, x ^ n = 1 → ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g = x := by
  first | exact @GlobalTheory.TorsLift.torsion_points_restrict_bijective | exact GlobalTheory.TorsLift.torsion_points_restrict_bijective | (intros; apply GlobalTheory.TorsLift.torsion_points_restrict_bijective <;> assumption)

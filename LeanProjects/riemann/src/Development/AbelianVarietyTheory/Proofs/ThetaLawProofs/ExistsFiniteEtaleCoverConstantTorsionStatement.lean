import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_cover_constant_torsion : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g n : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsUnit (n : R) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧ ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] [IsCommMonObj A₁] (φ : A₁.left ⟶ A.left), IsGrpPullback A₁ A (spMap (algebraMap R R₁)) φ → ∃ i : Multiplicative (Fin (2 * g) → ZMod n) →* (𝟙_ (Over (Sp R₁)) ⟶ A₁), (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R₁), (∀ x : Over.mk t ⟶ A₁, x ^ n = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1) := by
  first | exact @GlobalTheory.TorsionCover.exists_torsion_basis_cover | exact GlobalTheory.TorsionCover.exists_torsion_basis_cover | (intros; apply GlobalTheory.TorsionCover.exists_torsion_basis_cover <;> assumption)

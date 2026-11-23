import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
theorem _root_.GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X), M.IsLB → (∀ r r', SectionsHaveFiniteDimension p M r → SectionsHaveFiniteDimension p M r' → r = r') ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → (∀ r, SectionsHaveFiniteDimension p M r → SectionsHaveFiniteDimension p M' r) ∧ ∀ e, LBIso (lbPow M e) (lbPow M' e)) ∧ (∀ a e, LBIso (lbPow (lbPow M a) e) (lbPow M (a * e))) ∧ LBIso (lbPow M 1) M ∧ (∀ (Y : Scheme.{0}) (φ : Y ⟶ X) (e : ℕ), LBIso (lbPow (M.pull φ) e) ((lbPow M e).pull φ)) ∧ ∀ (Y : Scheme.{0}) (φ : Y ≅ X) (r : ℕ), SectionsHaveFiniteDimension p M r ↔ SectionsHaveFiniteDimension (φ.hom ≫ p) (M.pull φ.hom) r := by
  first | exact @GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant | exact GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant | (intros; apply GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNumberFieldPointSiegelFamilyKnownValue
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
theorem _root_.GlobalTheory.T.exists_numberField_point_siegelFamily_knownValue : Out.Laws → ThetaUnifAV → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → NumberField K → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (j : K →+* K₁) (σ₁ : K₁ →+* ℂ) (y : KeyIn K₁) (q : Sp K₁ ⟶ F.X) (φ : y.P.A.left ⟶ F.univ.A.left) (τ : Matrix (Fin h) (Fin h) ℂ), σ₁.comp j = σ ∧ q ≫ F.s = spMap j ∧ Known K₁ y ∧ SqOf y.P F.univ q φ ∧ PtAt F.univ (spMap σ₁ ≫ q) τ := by
  first | exact @GlobalTheory.KeyFam.exists_known_point | exact GlobalTheory.KeyFam.exists_known_point | (intros; apply GlobalTheory.KeyFam.exists_known_point <;> assumption)

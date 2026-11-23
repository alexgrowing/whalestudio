import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSiegelFamilyOverNumberField
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
theorem _root_.GlobalTheory.T.exists_siegelFamily_over_numberField : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ h : ℕ, 1 ≤ h → ∃ (k : ℕ) (K : Type) (_ : Field K) (_ : NumberField K) (ζ : K) (σ : K →+* ℂ), 3 ≤ k ∧ Odd k ∧ σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) ∧ Nonempty (SFam h k ζ) := by
  first | exact @GlobalTheory.SiegelFamilyNumberField.exists_sFam_numberField | exact GlobalTheory.SiegelFamilyNumberField.exists_sFam_numberField | (intros; apply GlobalTheory.SiegelFamilyNumberField.exists_sFam_numberField <;> assumption)

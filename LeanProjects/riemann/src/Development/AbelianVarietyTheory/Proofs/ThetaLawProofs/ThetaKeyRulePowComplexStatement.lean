import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRulePowComplex
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_pow_complex : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (x y : KeyIn ℂ) (j : ℕ), GlobalTheory.KeyPow.IsKeyPow y x j → κ ℂ y = κ ℂ x ^ j := by
  first | exact @GlobalTheory.KeyCl.value_pow_complex | exact GlobalTheory.KeyCl.value_pow_complex | (intros; apply GlobalTheory.KeyCl.value_pow_complex <;> assumption)

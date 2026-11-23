import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ThetaLineDualDegreeOfKeyFormulaPowerForm
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.SemistableReduction.LemmaH
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLine_dual_degree_of_keyFormulaPowerForm : GlobalTheory.KeyFormulaPow → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi) := by
  first | exact @GlobalTheory.thetaLine_dual_deg_of_keyFormulaPow | exact GlobalTheory.thetaLine_dual_deg_of_keyFormulaPow | (intros; apply GlobalTheory.thetaLine_dual_deg_of_keyFormulaPow <;> assumption)

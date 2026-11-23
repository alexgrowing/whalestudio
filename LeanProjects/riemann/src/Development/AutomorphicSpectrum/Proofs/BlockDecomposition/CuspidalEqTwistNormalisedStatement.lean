import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalEqTwistNormalised
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_eq_twist_normalised : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ (π : CuspSub E a), ∃ (π₀ : CuspSub E a) (χ : HChar E), IsNormalised π₀ ∧ π = π₀.twist χ := by
  first | exact @GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised | exact GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised | (intros; apply GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised <;> assumption)

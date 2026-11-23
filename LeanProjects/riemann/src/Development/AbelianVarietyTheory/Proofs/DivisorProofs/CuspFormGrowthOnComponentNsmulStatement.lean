import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGrowthOnComponentNsmul
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormGrowthOnComponent_nsmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G : WTZ E), Even G.2 → ∀ a : ℕ, 1 ≤ a → growthOn U Z (a • G) = (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
  first | exact @GlobalTheory.GrowthMul.growthOn_nsmul | exact GlobalTheory.GrowthMul.growthOn_nsmul | (intros; apply GlobalTheory.GrowthMul.growthOn_nsmul <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponent
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_lower_bound_bergmanFunction_on_component : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ D.R.r) ∈ framesOn (U σ) Z → ∀ β : ENNReal, (∀ (x0 : Frame ((U σ).X y.1).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((U σ).X y.1)))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U σ).X y.1) x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet ((U σ).X y.1) x0 FF → ∃ P ∈ ((U σ).X y.1).SS (modelWt (U σ) G y.1), P y.2.1 ≠ 0 ∧ β * ∫⁻ z in FF, ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X y.1) x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0) ≤ ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P y.2.1 ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0 FF) → β ≤ bergOn (U σ) (D.sp.W j) (dict σ) Z G y := by
  first | exact @GlobalTheory.BergLower.le_bergOn | exact GlobalTheory.BergLower.le_bergOn | (intros; apply GlobalTheory.BergLower.le_bergOn <;> assumption)

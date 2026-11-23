import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgHasType
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStabEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_avg_has_type : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @GlobalTheory.KFinCuspAvgType.isTypeAt_avgN | exact GlobalTheory.KFinCuspAvgType.isTypeAt_avgN | (intros; apply GlobalTheory.KFinCuspAvgType.isTypeAt_avgN <;> assumption)

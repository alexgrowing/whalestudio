import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothExtensionOfPhaseFunction
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_extension_of_phase_function : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ _ => ∀ (τ : D.what₂.Tau) c,
    ∃ g : (T.M c).Fun, (T.M c).Smooth g ∧
      ∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x := by
  first | exact @GlobalTheory.DetHodgeExt.exists_smooth_ext | exact GlobalTheory.DetHodgeExt.exists_smooth_ext | (intros; apply GlobalTheory.DetHodgeExt.exists_smooth_ext <;> assumption)

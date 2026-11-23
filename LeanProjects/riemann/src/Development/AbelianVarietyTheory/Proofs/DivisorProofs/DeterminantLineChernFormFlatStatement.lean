import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantLineChernFormFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_line_chern_form_flat : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ _ => ∀ (B : ℝ) (τ : D.what₂.Tau) c (g : (T.M c).Fun),
    (T.M c).Smooth g →
    (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
    ∀ σ, LeviEq ((T.M c).A σ)
      ((T.K B c).c1 (T.L B c (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) + (T.K B c).ar g) σ)
      (LocPot.ofFun fun _ => 0) := by
  first | exact @GlobalTheory.DetLineFlat.first_chern_form_determinant_line_eq_zero | exact GlobalTheory.DetLineFlat.first_chern_form_determinant_line_eq_zero | (intros; apply GlobalTheory.DetLineFlat.first_chern_form_determinant_line_eq_zero <;> assumption)

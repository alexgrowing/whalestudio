import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoMixedIntegralBoundary
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_mixed_integral_boundary : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (τ : D.what₂.Tau) c (u : Wt O.Y),
    DomL O.Y.j u → ∀ g : (T.M c).Fun, (T.M c).Smooth g →
      (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
      Filter.Tendsto (fun R => (T.M c).int (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar ((T.F c).phR R u)))
          ((T.F c).phR R (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0)) -
        (T.M c).int (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar ((T.F c).phR R u))) g) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.DetLineIntZero.tendsto_int_sub | exact GlobalTheory.DetLineIntZero.tendsto_int_sub | (intros; apply GlobalTheory.DetLineIntZero.tendsto_int_sub <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothBoundaryPotential
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_boundary_potential : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → OnObj fun D O _ T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (τ : D.what₂.Tau) c,
    ∃ g : (T.M c).Fun, (T.M c).Smooth g ∧
      (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) ∧
      ∀ (u : Wt O.Y) (f : (T.M c).Fun), (T.M c).Smooth f →
        (T.K B c).num (Fin.cons (T.L B c (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) + (T.K B c).ar g)
          fun _ => T.L B c u + (T.K B c).ar f) =
        (T.M c).int (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar f)) (fun _ _ => O.Y.htDetT B c τ) := by
  first | exact @GlobalTheory.FlatDetLine.numbers_eq_height_mul_degree | exact GlobalTheory.FlatDetLine.numbers_eq_height_mul_degree | (intros; apply GlobalTheory.FlatDetLine.numbers_eq_height_mul_degree <;> assumption)

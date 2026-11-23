import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MdiscEqZeroOfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormsInvariantUnderMetricChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothExtensionOfPhaseFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantLineChernFormFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantLineArithmeticIntersectionNumberStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.FlatDetLine

theorem numbers_eq_height_mul_degree : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB →
    OnObj fun D O _ T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (τ : D.what₂.Tau) c,
    ∃ g : (T.M c).Fun, (T.M c).Smooth g ∧
      (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) ∧
      ∀ (u : Wt O.Y) (f : (T.M c).Fun), (T.M c).Smooth f →
        (T.K B c).num (Fin.cons (T.L B c (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) + (T.K B c).ar g)
          fun _ => T.L B c u + (T.K B c).ar f) =
        (T.M c).int (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar f)) (fun _ _ => O.Y.htDetT B c τ) := by
  intro hX h1 h2 h3 D O hC hf A T H hr B hB τ c
  obtain ⟨g, hg, hgZ⟩ := GlobalTheory.DetHodgeExt.exists_smooth_ext h1 h2 D O hC hf A T H hr τ c
  refine ⟨g, hg, hgZ, fun u f hf' => ?_⟩
  rw [GlobalTheory.MixedDiscriminantZeroSlot.num_add_ar _ _ _ _ f hf' (GlobalTheory.T.determinant_line_chern_form_flat h1 h2 D O hC hf A T H hr B τ c g hg hgZ),
    GlobalTheory.T.determinant_line_arithmetic_intersection_number hX h1 h2 h3 D O hC hf A T H hr B hB τ c g hg hgZ u, GlobalTheory.MassConst.integral_chern_forms_invariant_under_metric_change _ _ _ f _ hf']

end GlobalTheory.FlatDetLine

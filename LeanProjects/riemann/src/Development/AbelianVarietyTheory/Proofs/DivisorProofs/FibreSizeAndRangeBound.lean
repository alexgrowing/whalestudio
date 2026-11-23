import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlurisubharmonicOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialLogGrowthBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialLogGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialVanishesFarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPlurisubharmonicCorrectionStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.InterpMetricObj

theorem ph_linear : OnObj fun _ O _ T _ _ => ∀ c σ x, x ∉ (T.M c).Z σ → IsLinearMap ℝ fun u => (T.F c).ph u σ x := by
  intro D O _ _ A T H h c σ x hx
  have e : (fun u => (T.F c).ph u σ x) = fun u => O.chg c none u _ ((h.man c).pt σ x) :=
    funext fun u => (h.an c).ph u σ x hx
  rw [e]
  refine ⟨fun u v => ?_, fun a u => ?_⟩
  · simp only [Setup.chg]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => add_mul (u i.1 i.2) (v i.1 i.2) _
  · simp only [Setup.chg, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_assoc a (u i.1 i.2) _

theorem size_inR : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c, (T.F c).Size ∧ (T.F c).InR O.Y.j := by
  intro h1 h2 D O hC hf A T H h c
  have hlog : ∀ σ x, x ∉ (T.M c).Z σ → 0 ≤ Real.log ((T.M c).r σ x) := fun σ x hx =>
    Real.log_nonneg (by linarith [Real.add_one_le_exp 1, ((T.M c).bd σ).2.2.2.2.2.1 x hx])
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.potential_log_growth_bound h1 h2 D O hC hf A T H h c
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.truncated_potential_log_growth h1 h2 D O hC hf A T H h c
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.T.truncated_potential_approximation h1 h2 D O hC hf A T H h c
  refine ⟨⟨ph_linear D O hC hf A T H h c, GlobalTheory.T.potential_smooth_off_boundary h1 h2 D O hC hf A T H h c, GlobalTheory.T.plurisubharmonic_off_boundary h1 h2 D O hC hf A T H h c,
    max C₁ C₂, fun u σ x hx => ⟨?_, fun R hR => ?_⟩⟩, fun σ => ?_⟩
  · refine (hC₁ u σ x hx).trans (mul_le_mul_of_nonneg_right ?_ (hlog σ x hx))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · refine (hC₂ u σ x hx R hR).trans (mul_le_mul_of_nonneg_right ?_ (hlog σ x hx))
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · obtain ⟨b, p, hP, C₄, hC₄⟩ := GlobalTheory.T.truncated_plurisubharmonic_correction h1 h2 D O hC hf A T H h c σ
    refine ⟨b, p, hP, max C₃ C₄, fun u R hR => ⟨GlobalTheory.T.truncated_potential_smooth h1 h2 D O hC hf A T H h c u σ R hR,
      fun hu => hC₄ _ (le_max_right _ _) u R hR hu, fun x hx => ⟨GlobalTheory.T.truncated_potential_vanishes_far h1 h2 D O hC hf A T H h c u σ R hR x hx,
      fun hr => (hC₃ u σ R hR x hx hr).trans ?_⟩⟩⟩
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (by linarith)

end GlobalTheory.InterpMetricObj

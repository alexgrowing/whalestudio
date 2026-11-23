import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.ProdFibre

theorem lintegral_pi_fibre : ∀ (T A B C : Type) [Fintype T] [MeasureSpace A] [MeasureSpace B] [MeasureSpace C] [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)] [SigmaFinite (volume : Measure C)] (g : A × B → C) (π : C → A) (D : C → ℝ≥0∞) (φ : (T → A) → ℝ≥0∞), MeasurePreserving g volume volume → Measurable π → (∀ w, π (g w) = w.1) → Measurable D → Measurable φ → ∫⁻ c : T → C, φ (fun t => π (c t)) * ∏ t, D (c t) = ∫⁻ a : T → A, φ a * ∏ t, ∫⁻ b, D (g (a t, b)) := by
  intro T A B C _ _ _ _ _ _ _ g π D φ hg hπ hgπ hD hφ
  have h1 : MeasurePreserving (fun (a : T → A × B) (t : T) => g (a t)) volume volume :=
    volume_preserving_pi (f := fun _ : T => g) (fun _ => hg)
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow A B T).symm
  have h3 := h1.comp h2
  have hF : Measurable (fun c : T → C => φ (fun t => π (c t)) * ∏ t, D (c t)) := by
    refine Measurable.mul (hφ.comp ?_) ?_
    · exact measurable_pi_lambda _ (fun t => hπ.comp (measurable_pi_apply t))
    · exact Finset.measurable_prod _ (fun t _ => hD.comp (measurable_pi_apply t))
  rw [← h3.lintegral_comp hF, Measure.volume_eq_prod]
  refine (lintegral_prod _ (hF.comp h3.measurable).aemeasurable).trans ?_
  refine lintegral_congr (fun a => ?_)
  have hm : ∀ t, Measurable (fun b : B => D (g (a t, b))) := fun t =>
    hD.comp (hg.measurable.comp measurable_prodMk_left)
  have hin := GlobalTheory.SnMass.Push.lintegral_fintype_prod (X := fun _ : T => B)
    (μ := fun _ => (volume : Measure B)) (fun t b => D (g (a t, b))) hm
  rw [← hin, ← volume_pi, ← lintegral_const_mul]
  · refine lintegral_congr (fun b => ?_)
    change φ (fun t => π (g (a t, b t))) * ∏ t, D (g (a t, b t)) = _
    simp only [hgπ]
  · exact Finset.measurable_prod _ (fun t _ => (hm t).comp (measurable_pi_apply t))

end GlobalTheory.ProdFibre

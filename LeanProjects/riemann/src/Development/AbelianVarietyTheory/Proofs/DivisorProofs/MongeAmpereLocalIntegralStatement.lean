import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereLocalIntegral
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_local_integral : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (P : LocPot X) (O : Set X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (j : Fin A.n) (r : ℝ), IsOpen O → IsPotentialOn A O P → IsCompatChart A ψ → Metric.ball (0 : Fin e → ℂ) r ⊆ ψ.target → (∀ z ∈ Metric.ball (0 : Fin e → ℂ) r, ψ.symm z ∈ (A.chart j).source) → ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' (ψ.symm '' Metric.ball (0 : Fin e → ℂ) r ∩ O), ENNReal.ofReal (locDens A (fun _ => P) j y) ≤ ∫⁻ z in Metric.ball (0 : Fin e → ℂ) r ∩ ψ.symm ⁻¹' O, ENNReal.ofReal (maDens (fun _ => P.φ (ψ.symm z) ∘ ψ.symm) z) := by
  first | exact @GlobalTheory.lintegral_locDens_le_compatChart | exact GlobalTheory.lintegral_locDens_le_compatChart | (intros; apply GlobalTheory.lintegral_locDens_le_compatChart <;> assumption)

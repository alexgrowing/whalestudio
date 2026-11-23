import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem stepGap_torus : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) →
    (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → stepGap M BM p (fun q => c q.1 * z q) = stepGap M BM p z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p z c hc hz
  have hpos : 0 < ∏ k, ‖c k‖ ^ M.dy p k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  have h1 := (BM.hom p).smul c z hc
  rw [BM.hom_deg p] at h1
  have h2 : (fsHerm ι (M.dy p)).h (fun q => c q.1 * z q) =
      (∏ k, ‖c k‖ ^ M.dy p k) * (fsHerm ι (M.dy p)).h z := (fsHerm ι (M.dy p)).smul c z hc
  unfold stepGap
  rw [h1, h2, Real.log_mul hpos.ne' ((BM.hom p).pos z hz).ne',
    Real.log_mul hpos.ne' ((fsHerm ι (M.dy p)).pos z hz).ne']
  ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW

import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.WeilBound.CoreStatements.RationalSupMetrics.AevalEqZeroOfMem

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem MultiProjectiveCoordinates.levi_shift {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) (t : ℝ)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    leviForm (fun z => Real.log ((shiftH A t).h z)) z w = leviForm (fun z => Real.log (A.h z)) z w := by
  have h1 : (fun z => Real.log ((shiftH A t).h z)) =ᶠ[𝓝 z] fun z => t + Real.log (A.h z) := by
    filter_upwards [MultiProjectiveCoordinates.isOpen_blocks.mem_nhds hz] with z' hz'
    show Real.log (Real.exp t * A.h z') = _
    rw [Real.log_mul (Real.exp_pos t).ne' (A.pos z' hz').ne', Real.log_exp]
  have h2 : fderiv ℝ (fun z => t + Real.log (A.h z)) = fderiv ℝ (fun z => Real.log (A.h z)) :=
    funext fun z => fderiv_const_add t
  unfold leviForm
  rw [h1.fderiv.fderiv_eq, h2]

theorem MultiProjectiveCoordinates.shiftH_smooth_nef_gen : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (t Λ : ℝ), (IsSmoothHerm A → IsSmoothHerm (shiftH A t)) ∧ (IsNefH P A → IsNefH P (shiftH A t)) ∧ (IsGenH P A Λ → IsGenH P (shiftH A t) (Λ * Real.exp (-t))) := by
  intro K _ ι _ P A t Λ
  have hs : IsSmoothHerm A → IsSmoothHerm (shiftH A t) := fun h => contDiffOn_const.mul h
  have hp : (∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P A) →
      ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P (shiftH A t) := by
    rintro ⟨P0, h0, h1, h2⟩
    refine ⟨P0, h0, hs h1, fun z hz w hw => ?_⟩
    rw [MultiProjectiveCoordinates.levi_shift A t hz.1]
    exact h2 z hz w hw
  have hc : IsConjInvariantH A → IsConjInvariantH (shiftH A t) := fun h z => by
    show Real.exp t * _ = Real.exp t * _
    rw [h z]
  refine ⟨hs, fun h => ⟨hp h.semipos, hc h.conj, h.nef⟩, fun h =>
    ⟨mul_pos h.pos (Real.exp_pos _), hp h.semipos, hc h.conj, ?_⟩⟩
  obtain ⟨a, ha, hm⟩ := h.mono
  refine ⟨a, ha, fun z hz μ hμ => (hm z hz μ hμ).trans_eq ?_⟩
  show Λ * A.h z = Λ * Real.exp (-t) * (Real.exp t * A.h z)
  rw [mul_assoc, ← mul_assoc (Real.exp (-t)), ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

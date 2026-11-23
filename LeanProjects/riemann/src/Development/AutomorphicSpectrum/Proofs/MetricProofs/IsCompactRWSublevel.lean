import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem continuous_normSec {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L) (hS : IsSection A L s) :
    Continuous (fun y => ‖s y y‖ * Real.exp (-L.φ y y)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc := LeviFormBoundaryTopology.continuousAt_of_holoOn A (hS.1 x) (L.mem_U x)
  have hφ := LeviFormBoundaryTopology.continuousAt_of_smoothOn A (L.isOpen_U x) (hL.1 x) (L.mem_U x)
  have hF : ContinuousAt (fun z => ‖s x z‖ * Real.exp (-L.φ x z)) x :=
    hc.norm.mul (Real.continuous_exp.continuousAt.comp hφ.neg)
  refine hF.congr ?_
  filter_upwards [(L.isOpen_U x).mem_nhds (L.mem_U x)] with z hz
  exact hS.2 x z z ⟨hz, L.mem_U z⟩

theorem isCompact_rW_sublevel : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → ∀ R : ℝ, IsCompact {y | y ∉ bdry s ∧ rW L s y ≤ R} := by
  intro e X _ _ _ A L s hL hS R
  have hset : {y | y ∉ bdry s ∧ rW L s y ≤ R} =
      {y | Real.exp ((Real.exp 1 - R) / 2) ≤ ‖s y y‖ * Real.exp (-L.φ y y)} := by
    ext y
    simp only [Set.mem_setOf_eq, bdry, rW, logNormSec]
    constructor
    · rintro ⟨h0, h1⟩
      have hpos : 0 < ‖s y y‖ * Real.exp (-L.φ y y) :=
        mul_pos (norm_pos_iff.2 h0) (Real.exp_pos _)
      exact (Real.le_log_iff_exp_le hpos).1 (by linarith)
    · intro h
      have hpos : 0 < ‖s y y‖ * Real.exp (-L.φ y y) := lt_of_lt_of_le (Real.exp_pos _) h
      have h0 : s y y ≠ 0 := by
        intro h0
        simp [h0] at hpos
      have h1 := (Real.le_log_iff_exp_le hpos).2 h
      exact ⟨h0, by linarith⟩
  rw [hset]
  exact (isClosed_le continuous_const (continuous_normSec A L s hL hS)).isCompact

end GlobalTheory.CompanionTheory.Ar.Giv

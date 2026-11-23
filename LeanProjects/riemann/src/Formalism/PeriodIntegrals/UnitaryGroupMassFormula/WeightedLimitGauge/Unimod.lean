import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TBallMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstPair

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def UnitInv : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ q ∈ UWb k r, qᴴ * q = 1 → ν.map (rmulM q) = ν

def HermInv : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ B₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, B₀ᴴ * Hb k * B₀ = Hb k → B₀ᴴ = B₀ →
      ν.map (rmulM (embWb k r B₀)) = ν

def PolarDecW : Prop :=
  ∀ (k r : ℕ) (p : Mat k r), p ∈ UWb k r → ∃ B₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
    B₀ᴴ * Hb k * B₀ = Hb k ∧ B₀ᴴ = B₀ ∧ ∃ q ∈ UWb k r, qᴴ * q = 1 ∧ p = embWb k r B₀ * q

theorem rmulM_comp {k r : ℕ} (a b : Mat k r) : rmulM b ∘ rmulM a = rmulM (a * b) := by
  funext x
  show Matrix.of x * a * b = Matrix.of x * (a * b)
  rw [Matrix.mul_assoc]

theorem rmulM_meas {k r : ℕ} (p : Mat k r) : Measurable (rmulM p : Mt k r → Mt k r) :=
  (rmulM_cont p).measurable

theorem unimodW_of (hU : UnitInv) (hH : HermInv) (hP : PolarDecW) : UnimodW := by
  intro k r ν hk hG p hp
  obtain ⟨B₀, hB, hBh, q, hq, hqu, rfl⟩ := hP k r p hp
  rw [← rmulM_comp, ← Measure.map_map (rmulM_meas q) (rmulM_meas _), hH k r ν hk hG B₀ hB hBh,
    hU k r ν hk hG q hq hqu]

end PI.RhsWLim.W

import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ChartJac
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def psiE (k r : ℕ) (T' : ℝ) (q : TrE k) : (Fin k → ℂ) × ℂ :=
  opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')

def kapT (k : ℕ) (v : (Fin k → ℂ) × ℂ) : TrE k :=
  (WithLp.equiv 2 (Option (Fin k × Bool) → ℝ)).symm (fun o => match o with
    | none => Complex.arg v.2
    | some (a, b) => if b then (v.1 a).im else (v.1 a).re)

def phiT (k r : ℕ) (T' : ℝ) (q : TrE k) : TrE k := kapT k (psiE k r T' q)

def HypChart : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε →
    hypM k T' (opE k r T' ρ) = (1 / 2) * volume (phiT k r T' '' Metric.ball 0 ρ)

def PhiDiff : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' →
    ContDiffAt ℝ 1 (phiT k r T') 0 ∧ (fderiv ℝ (phiT k r T') 0).det = (T' / 2) ^ k

theorem hypLocal_of (hJ : ChartJac) (hC : HypChart) (hD : PhiDiff) : HypLocal := by
  intro k r T' hk hT
  obtain ⟨hcd, hdet⟩ := hD k r T' hk hT
  obtain ⟨ε, hε, hV⟩ := hC k r T' hk hT
  have hdet0 : (fderiv ℝ (phiT k r T') 0).det ≠ 0 := by
    rw [hdet]; exact pow_ne_zero _ (by positivity)
  have hlim := hJ (TrE k) (phiT k r T') volume (fun _ => 1) hcd hdet0
    continuousAt_const ENNReal.one_ne_top ⟨Set.univ, Filter.univ_mem, fun A _ _ => by simp⟩
  have key := hlim.const_mul (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) * ((1 : ℝ≥0∞).toReal * |(fderiv ℝ (phiT k r T') 0).det|) =
      T' ^ k / 2 ^ (k + 1) := by
    rw [hdet, ENNReal.toReal_one, one_mul, abs_of_pos (by positivity), div_pow, pow_succ]
    field_simp
    try ring
  rw [hval] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hε)] with ρ hρ0 hρε
  rw [hV ρ hρ0 hρε, tVol, ENNReal.toReal_mul, mul_div_assoc]
  congr 1
  simp

end PI.RhsWLim.W

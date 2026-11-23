import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUDensity
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.IntegralGaussEOmPhiOmE
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.BridgeA

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def cOmega (N : ℕ) : ℝ := 1 / (2 ^ (N * (N - 1) / 2) * volU N)

theorem cOmega_pos (N : ℕ) : 0 < cOmega N := by
  have hv : 0 < volU N := by
    unfold volU
    apply Finset.prod_pos
    intro i _
    have hf : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hp : (0 : ℝ) < Real.pi ^ (i + 1) := pow_pos Real.pi_pos _
    exact div_pos (mul_pos two_pos hp) hf
  unfold cOmega
  exact div_pos one_pos (mul_pos (pow_pos two_pos _) hv)

theorem omegaDensity_haarProb (μ : Measure (Formalism.BasicNotions.UpqT N 0)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    Formalism.BasicNotions.OmegaDensity μ (ENNReal.ofReal (cOmega N)) :=
  PolarCoordinateComparison.omegaDensity_main μ

theorem omegaDensity_cd (cd : Formalism.BasicNotions.CDHaar) (N : ℕ) :
    Formalism.BasicNotions.OmegaDensity (cd.cd N 0) (ENNReal.ofReal (cOmega N)) := by
  haveI := cd.haar N 0
  haveI := cd.prob N
  exact omegaDensity_haarProb (cd.cd N 0)

end ReciprocityTheory.ChartRestriction.DS

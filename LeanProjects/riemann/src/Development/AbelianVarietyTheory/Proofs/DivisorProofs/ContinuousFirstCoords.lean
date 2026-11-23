import Mathlib
import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

noncomputable section

namespace GlobalTheory.SphereMeanDrop

open MeasureTheory Set

def gaussProb (n : ℕ) : Measure (EuclideanSpace ℂ (Fin n)) :=
  ProbabilityTheory.cond ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2))) univ

def radProb (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  ProbabilityTheory.cond ((Measure.volumeIoiPow (2 * n - 1)).withDensity
    fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ

def firstCoords {N n : ℕ} (h : N ≤ n) (x : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun j => WithLp.ofLp x (Fin.castLE h j)

end GlobalTheory.SphereMeanDrop

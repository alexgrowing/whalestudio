import Mathlib
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.HCXi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

def Kset (k r : ℕ) : Set (Mat k r) := {g | g ∈ GV k r ∧ gᴴ * g = 1}

def isoVec (k r : ℕ) : Fin (2 * r + k + 1) → ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (bvec (wI k r 0) + bvec (wI k r (Fin.last k)))

def frame (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i a => fvec k r (isoVec k r) a i

def Pset (k r : ℕ) : Set (Mat k r) :=
  {p | p ∈ GV k r ∧ ∃ u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
    u.BlockTriangular id ∧ p * frame k r = frame k r * u}

def gram (k r : ℕ) (g : Mat k r) (a : Fin (r + 1)) : ℝ :=
  (((g * frame k r)ᴴ * (g * frame k r)).submatrix (Fin.castLE (Nat.succ_le_of_lt a.isLt))
    (Fin.castLE (Nat.succ_le_of_lt a.isLt))).det.re

def vHalf (k r : ℕ) (g : Mat k r) : ℝ :=
  (∏ a : Fin r, (gram k r g a.castSucc)⁻¹) * gram k r g (Fin.last r) ^ (-((k : ℝ) / 2))

def IsKMeas (k r : ℕ) (μK : Measure (Mt k r)) : Prop := IsHaarOn (Kset k r) μK ∧ μK Set.univ = 1

def XiE (k r : ℕ) (μK : Measure (Mt k r)) (g : Mat k r) : ℝ≥0∞ :=
  ∫⁻ κ : Mt k r, ENNReal.ofReal (vHalf k r (g * Matrix.of κ)) ∂μK

def Xi (k r : ℕ) (μK : Measure (Mt k r)) (g : Mat k r) : NNReal := (XiE k r μK g).toNNReal

def sqLen {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

end GlobalTheory.HCXi

import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
import Development.WeilBound.RepresentationTheoryGL.StandardBasisDerivatives.ArchimedeanBasisDerivatives.StBasDeriv

noncomputable section

open MvPolynomial Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw

namespace GlobalTheory.CompanionTheory.TwistHomotopy

variable {n : ℕ}

theorem hb_conjTranspose (p : Fin n × Fin n) : (hb p)ᴴ = hb p := by
  unfold hb
  split_ifs with h1 h2
  · simp
  · simp [conjTranspose_smul, conjTranspose_add, add_comm]
  · have e : star (((Real.sqrt 2 : ℂ))⁻¹ * Complex.I) = -(((Real.sqrt 2 : ℂ))⁻¹ * Complex.I) := by
      simp
    rw [conjTranspose_smul, conjTranspose_sub, e]
    simp [neg_smul, smul_sub]
    abel

def kern (F : ℝ → ℝ) (a : ℝ) (j : ℕ) (x v : ℝ) : ℝ :=
  Real.exp (a * v) * iteratedDeriv j F (Real.exp (2 * v) * x)

def homot (F : ℝ → ℝ) (a : ℝ) (j : ℕ) (v₁ v₂ x : ℝ) : ℝ := ∫ v in v₂..v₁, kern F a j x v

def ex (N k : ℕ) : ℝ := 2 * (k : ℝ) - N

end GlobalTheory.CompanionTheory.TwistHomotopy

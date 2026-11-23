import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.growthLoc
import Mathlib

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace Ad3.GA.Gr

def fv (v : Pl) : ℚ →+* Qv v := (finEval v).comp (algebraMap ℚ 𝔸[ℚ])

def fw (w : InfinitePlace ℚ) : ℚ →+* w.Completion := (infEval w).comp (algebraMap ℚ 𝔸[ℚ])

def xq (γ : GL (Fin 2) ℚ) : Fin 3 → ℚ :=
  ![(γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1, -(γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0, 0]

theorem conv {X d β0 β1 β2 na nb nab H c : ℝ} (hβ1 : 0 < β1) (hβ2 : 0 < β2)
    (ha : na * β1 = β0) (hb : nb * β2 = β1) (hab : nab * β2 = β0)
    (h1 : X * β2 ≤ c ^ 5 * H ^ 6 * β1) (h2 : d * β1 ≤ c ^ 7 * H ^ 6 * X ^ 2 * β0)
    (h3 : d * β2 ≤ c ^ 3 * H ^ 2 * X * β0) :
    X ≤ c ^ 5 * H ^ 6 * nb ∧ d ≤ c ^ 7 * H ^ 6 * X ^ 2 * na ∧ d ≤ c ^ 3 * H ^ 2 * X * nab := by
  refine ⟨?_, ?_, ?_⟩
  · refine le_of_mul_le_mul_right ?_ hβ2
    rw [mul_assoc, hb]; exact h1
  · refine le_of_mul_le_mul_right ?_ hβ1
    rw [mul_assoc, ha]; exact h2
  · refine le_of_mul_le_mul_right ?_ hβ2
    rw [mul_assoc, hab]; exact h3

def Dv (Bd : Pl → ℝ) (g : G3) (v : Pl) : ℝ := locHeight (finAt v g) ^ 18 * Bd v ^ 3

end Ad3.GA.Gr

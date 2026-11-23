import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.growthLoc
import Mathlib

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace Ad3.K.GA.Gr

open Ad3.GA.Gr

variable {K : Type} [Field K] [NumberField K]

set_option linter.unusedSectionVars false

def fv (v : PlK K) : K →+* Kv K v := (finEval v).comp (algebraMap K 𝔸[K])

def fw (w : InfinitePlace K) : K →+* w.Completion := (infEval w).comp (algebraMap K 𝔸[K])

def xq (γ : GL (Fin 2) K) : Fin 3 → K :=
  ![(γ : Matrix (Fin 2) (Fin 2) K) 1 1, -(γ : Matrix (Fin 2) (Fin 2) K) 1 0, 0]

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

def Dv (Bd : PlK K → ℝ) (g : G3K K) (v : PlK K) : ℝ := locHeight (finAt v g) ^ 18 * Bd v ^ 3

end Ad3.K.GA.Gr

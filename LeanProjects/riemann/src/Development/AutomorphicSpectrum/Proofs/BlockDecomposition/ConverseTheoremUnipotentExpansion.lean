import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair vecCoeff)
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.GAUnfold

instance countable_GL2 : Countable (GL (Fin 2) ℚ) :=
  Function.Injective.countable (f := fun (u : GL (Fin 2) ℚ) (i j : Fin 2) => u.val i j)
    (fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))

def dA (a : ℚˣ) : GL (Fin 2) ℚ := ⟨!![(a : ℚ), 0; 0, 1], !![((a⁻¹ : ℚˣ) : ℚ), 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

end GlobalTheory.CompanionTheory.GAUnfold

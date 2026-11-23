import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair vecCoeff)
open scoped NumberField.AdeleRing
open scoped Classical

namespace GlobalTheory.CompanionTheory.GAUnfoldK

variable {K : Type} [Field K] [NumberField K]

theorem countable_number_field : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

instance countable_GL2 : Countable (GL (Fin 2) K) :=
  haveI : Countable K := countable_number_field
  Function.Injective.countable (f := fun (u : GL (Fin 2) K) (i j : Fin 2) => u.val i j)
    (fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))

def dA (a : Kˣ) : GL (Fin 2) K := ⟨!![(a : K), 0; 0, 1], !![((a⁻¹ : Kˣ) : K), 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

end GlobalTheory.CompanionTheory.GAUnfoldK

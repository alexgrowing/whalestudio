import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.GA.WhitU

abbrev idl (a : ℚˣ) : (𝔸[ℚ])ˣ := Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom a

theorem dia_dg (a : ℚˣ) : dia (dg a 1 1) = (dg (idl a) 1 1 : G3) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dia, dg, idl, AdelicGLn.diagonal]

theorem conj (a : ℚˣ) (x : 𝔸[ℚ]) : (dg (idl a) 1 1 : G3) * uni x 0 0 =
    uni (algebraMap ℚ 𝔸[ℚ] a * x) 0 0 * (dg (idl a) 1 1 : G3) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg, uni, Matrix.mul_apply, Fin.sum_univ_three, idl]

theorem pt {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) {W : G3 → ℂ} (hW : W ∈ V) (a : ℚˣ) (g : G3)
    (x : 𝔸[ℚ]) :
    W (dia (dg a 1 1) * (uni x 0 0 * g)) * (adelicChar ℚ (-x) : ℂ) =
      W (dg (idl a) 1 1 * g) * (adelicChar ℚ (algebraMap ℚ 𝔸[ℚ] ((a : ℚ) - 1) * x) : ℂ) := by
  have e : dia (dg a 1 1) * (uni x 0 0 * g) =
      uni (algebraMap ℚ 𝔸[ℚ] a * x) 0 0 * (dg (idl a) 1 1 * g) := by
    rw [dia_dg, ← mul_assoc, conj, mul_assoc]
  have e2 : algebraMap ℚ 𝔸[ℚ] ((a : ℚ) - 1) * x = algebraMap ℚ 𝔸[ℚ] a * x + -x := by
    rw [map_sub, map_one]; ring
  rw [e, hV.psi W hW, e2, add_zero, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

end GlobalTheory.CompanionTheory.GA.WhitU

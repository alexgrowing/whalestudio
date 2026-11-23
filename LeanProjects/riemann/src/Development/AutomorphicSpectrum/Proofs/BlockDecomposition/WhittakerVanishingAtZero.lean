import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.DoubleTate

theorem quasiCharExponent_eq_zero {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {χ : Fˣ →* ℂˣ} (h : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) :
    quasiCharExponent χ = 0 := by
  simp [quasiCharExponent, h]

theorem sdz : SDZ := by
  intro F _ _ _ _ _ _ f hf G hG α β hα hβ s hs
  let P : Fˣ → ℂ := fun u => f u * ((α u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ s
  let Q : Fˣ → ℂ := fun u => G u * (((α * β⁻¹) u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ s
  have hγ : Continuous (α * β⁻¹) := by
    have : ⇑(α * β⁻¹) = fun x => α x * (β x)⁻¹ := by
      funext x; simp
    rw [this]
    exact hα.1.mul hβ.1.inv
  have hγ1 : ∀ x, ‖(((α * β⁻¹) x : ℂˣ) : ℂ)‖ = 1 := by
    intro x
    simp [hα.2, hβ.2]
  have hP : Integrable P (multHaar F) :=
    integrable_localZeta hf hα.1 (by rw [quasiCharExponent_eq_zero hα.2]; simpa using hs)
  have hQ : Integrable Q (multHaar F) :=
    integrable_localZeta hG hγ (by rw [quasiCharExponent_eq_zero hγ1]; simpa using hs)
  have hPQ : Integrable (fun z : Fˣ × Fˣ => P z.1 * Q z.2) ((multHaar F).prod (multHaar F)) :=
    hP.mul_prod hQ
  have me := measurePreserving_mul_prod_inv (multHaar F) (multHaar F)
  have h1 : Integrable (fun z : Fˣ × Fˣ => P (z.2 * z.1) * Q z.1⁻¹)
      ((multHaar F).prod (multHaar F)) := me.integrable_comp_of_integrable hPQ
  have h2 : Integrable (fun z : Fˣ × Fˣ => P (z.1 * z.2) * Q z.2⁻¹)
      ((multHaar F).prod (multHaar F)) := h1.swap
  have key : ∀ a h : Fˣ, ((α a : ℂˣ) : ℂ) * mp a s *
      (((β h : ℂˣ) : ℂ) * f ((h : F) * a) * G ((h⁻¹ : Fˣ) : F)) = P (a * h) * Q h⁻¹ := by
    intro a h
    have hm : ((modulus (((a * h : Fˣ)) : F) : ℝ) : ℂ) ^ s *
        ((modulus (((h⁻¹ : Fˣ)) : F) : ℝ) : ℂ) ^ s = mp a s := by
      rw [← Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
      have hmm : ((modulus (((a * h : Fˣ)) : F) : ℝ)) * (modulus (((h⁻¹ : Fˣ)) : F) : ℝ) =
          modulus (a : F) := by
        rw [← NNReal.coe_mul, ← modulus_mul]
        congr 2
        simp
      rw [mp, ← Complex.ofReal_mul, hmm]
    have hc : ((α (a * h) : ℂˣ) : ℂ) * (((α * β⁻¹) h⁻¹ : ℂˣ) : ℂ) =
        ((α a : ℂˣ) : ℂ) * ((β h : ℂˣ) : ℂ) := by
      have : α (a * h) * (α * β⁻¹) h⁻¹ = α a * β h := by
        simp [mul_comm, mul_left_comm]
      exact_mod_cast congrArg Units.val this
    simp only [P, Q]
    rw [← hm, show ((a * h : Fˣ) : F) = (h : F) * a by simp [mul_comm]]
    linear_combination (-(f ((h : F) * a) * G ((h⁻¹ : Fˣ) : F) *
      ((modulus ((h : F) * a) : ℝ) : ℂ) ^ s * ((modulus (((h⁻¹ : Fˣ)) : F) : ℝ) : ℂ) ^ s)) * hc
  have hin : ∀ a : Fˣ, ((α a : ℂˣ) : ℂ) * mp a s *
      (∫ h : Fˣ, ((β h : ℂˣ) : ℂ) * f ((h : F) * a) * G ((h⁻¹ : Fˣ) : F) ∂multHaar F) =
      ∫ h : Fˣ, P (a * h) * Q h⁻¹ ∂multHaar F := by
    intro a
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun h => key a h)
  refine ⟨?_, ?_⟩
  · simp only [hin]
    exact h2.integral_prod_left
  · simp only [hin]
    rw [← integral_prod (fun z : Fˣ × Fˣ => P (z.1 * z.2) * Q z.2⁻¹) h2]
    have e1 : ∫ z : Fˣ × Fˣ, P (z.1 * z.2) * Q z.2⁻¹ ∂((multHaar F).prod (multHaar F)) =
        ∫ z : Fˣ × Fˣ, P (z.2 * z.1) * Q z.1⁻¹ ∂((multHaar F).prod (multHaar F)) :=
      integral_prod_swap (fun z : Fˣ × Fˣ => P (z.2 * z.1) * Q z.1⁻¹)
    have e2 : ∫ z : Fˣ × Fˣ, P (z.2 * z.1) * Q z.1⁻¹ ∂((multHaar F).prod (multHaar F)) =
        ∫ z : Fˣ × Fˣ, P z.1 * Q z.2 ∂((multHaar F).prod (multHaar F)) := by
      conv_rhs => rw [← me.map_eq]
      exact (integral_map me.measurable.aemeasurable
        (by rw [me.map_eq]; exact hPQ.1)).symm
    rw [e1, e2, integral_prod_mul]
    rfl

end GlobalTheory.CompanionTheory.DoubleTate

import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.WhittakerIwasawa

theorem diagonal_mul_unipotent {F : Type} [Field F] (t₁ t₂ : Fˣ) (x : F) :
    Ad3.dg2 t₁ t₂ * Ad3.uni2 x =
      Ad3.uni2 ((t₁ : F) * x * ((t₂⁻¹ : Fˣ) : F)) * Ad3.dg2 t₁ t₂ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.uni2, Ad3.dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

theorem diagonal_mul_diagonal_alt {F : Type} [Field F] (t₁ t₂ b₁ b₂ : Fˣ) :
    Ad3.dg2 t₁ t₂ * Ad3.dg2 b₁ b₂ =
      Ad3.dg2 (t₂ * b₂) (t₂ * b₂) * Ad3.dg2 (t₁ * b₁ * (t₂ * b₂)⁻¹) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg2, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem whittaker_bound_iwasawa :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (C : ℝ), (∀ x g, W' (Ad3.uni2 x * g) = (ψ x : ℂ) * W' g) → (∀ (a : Fˣ) g, W' (Ad3.dg2 a a * g) = W' g) → (∀ (a : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 a 1 * κ)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 4 : ℝ)) → ∀ (t₁ t₂ b₁ b₂ : Fˣ) (x : F), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 t₁ t₂ * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ))‖ ≤ C * (modulus ((t₁ * b₁ * (t₂ * b₂)⁻¹ : Fˣ) : F) : ℝ) ^ (1 / 4 : ℝ) := by
  intro F _ _ _ _ ψ W' C hu hd hb t₁ t₂ b₁ b₂ x κ hκ
  have e : Ad3.dg2 t₁ t₂ * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ) =
      Ad3.uni2 ((t₁ : F) * x * ((t₂⁻¹ : Fˣ) : F)) * (Ad3.dg2 (t₂ * b₂) (t₂ * b₂) *
        (Ad3.dg2 (t₁ * b₁ * (t₂ * b₂)⁻¹) 1 * κ)) := by
    rw [← mul_assoc (Ad3.dg2 (t₂ * b₂) (t₂ * b₂)), ← diagonal_mul_diagonal_alt, ← mul_assoc, ← mul_assoc,
      ← mul_assoc, diagonal_mul_unipotent]
    simp only [mul_assoc]
  rw [e, hu, hd, norm_mul, Circle.norm_coe, one_mul]
  exact hb _ κ hκ

end GlobalTheory.CompanionTheory.WhittakerIwasawa

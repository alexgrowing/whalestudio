import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
import GroundTheory.AutomorphicForms.GL2.GodementSectionLocal

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3

section Mat

variable {R : Type*} [CommRing R]

def uni2 (x : R) : GL (Fin 2) R :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def dg2 (a b : Rˣ) : GL (Fin 2) R :=
  ⟨!![(a : R), 0; 0, b], !![((a⁻¹ : Rˣ) : R), 0; 0, (b⁻¹ : Rˣ)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def w0 : GL (Fin 2) R :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

end Mat

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def W2 (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) (g : GL (Fin 2) F) : ℂ :=
  ((μ₂ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (1 / 2) *
    ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      (∫ x, φ (![(h : F), h * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ) ∂multHaar F

def V2 (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) : Submodule ℂ (GL (Fin 2) F → ℂ) :=
  Submodule.span ℂ (W2 ψ μ₁ μ₂ '' GodementSectionLocal.schwartzBruhat2 F)

structure WhittakerModelGL2 (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (V : Submodule ℂ (GL (Fin 2) F → ℂ)) : Prop where
  ne : ∃ W ∈ V, W 1 ≠ 0
  stable : ∀ W ∈ V, ∀ h, (fun g => W (g * h)) ∈ V
  psi : ∀ W ∈ V, ∀ x g, W (uni2 x * g) = (ψ x : ℂ) * W g
  cen : ∀ W ∈ V, ∀ (a : Fˣ) g, W (dg2 a a * g) = ((μ₁ a * μ₂ a : ℂˣ) : ℂ) * W g
  smooth : ∀ W ∈ V, ∃ U : OpenSubgroup (GL (Fin 2) F), ∀ g, ∀ u ∈ U, W (g * u) = W g
  bound : ∀ W ∈ V, ∀ ε : ℝ, 0 < ε → ∃ C B : ℝ, ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
    ‖W (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧ (W (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)
  fe : ∀ W ∈ V, ∀ c, IsUnit1 c → ∀ s : ℂ, 0 < s.re → s.re < 1 →
    ∫ a, W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F =
      gam ψ (μ₁ * c) s * gam ψ (μ₂ * c) s * ∫ a, W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F

def Loc2 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (ψ : AddChar F Circle), IsStd ψ → ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → WhittakerModelGL2 ψ μ₁ μ₂ (V2 ψ μ₁ μ₂) ∧
    (IsUnramifiedChar μ₁ → IsUnramifiedChar μ₂ →
      W2 ψ μ₁ μ₂ (Set.indicator {x | ∀ i, x i ∈ 𝒪[F]} 1) =
        Spherical.sphericalWhittaker (Circle.coeHom.compAddChar ψ) ![μ₁ (unifUnit F), μ₂ (unifUnit F)])

end Ad3

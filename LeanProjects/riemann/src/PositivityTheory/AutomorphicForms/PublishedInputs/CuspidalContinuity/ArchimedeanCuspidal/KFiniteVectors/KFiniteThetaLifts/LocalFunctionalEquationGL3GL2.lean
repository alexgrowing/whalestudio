import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3

section Mat

variable {R : Type*} [CommRing R]

def d2 (a b : Rˣ) : GL (Fin 2) R :=
  ⟨!![(a : R), 0; 0, b], !![((a⁻¹ : Rˣ) : R), 0; 0, (b⁻¹ : Rˣ)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def n2 (x : R) : GL (Fin 2) R :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def w2 : GL (Fin 2) R :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def w3 : GL (Fin 3) R :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def bd : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 3) (Fin 3) R where
  toFun A := !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' A B := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def e3 : GL (Fin 2) R →* GL (Fin 3) R := Units.map bd

def ti {n : Type*} [Fintype n] [DecidableEq n] (g : GL n R) : GL n R :=
  ⟨g.inv.transpose, g.val.transpose, by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one]⟩

end Mat

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def mu32 (ψ : AddChar F Circle) : Measure ((Fˣ × Fˣ) × GL (Fin 2) F) :=
  ((multHaar F).prod (multHaar F)).prod ((LFS.hG ψ).restrict (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)))

def z32 (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (s : ℂ) (p : (Fˣ × Fˣ) × GL (Fin 2) F) : ℂ :=
  W (dg (p.1.1 * p.1.2) p.1.2 1 * e3 p.2) * W' (d2 (p.1.1 * p.1.2) p.1.2 * p.2) * mp p.1.1 (s - 3 / 2) * mp p.1.2 (2 * s - 1)

def dW3 (W : GL (Fin 3) F → ℂ) (g : GL (Fin 3) F) : ℂ := W (w3 * ti g)
def dW2 (W' : GL (Fin 2) F → ℂ) (h : GL (Fin 2) F) : ℂ := W' (w2 * ti h)

structure WhJL (ψ : AddChar F Circle) (ω : Fˣ →* ℂˣ) (γ : (Fˣ →* ℂˣ) → ℂ → ℂ) (T : Submodule ℂ (GL (Fin 2) F → ℂ)) :
    Prop where
  stable : ∀ W ∈ T, ∀ h, (fun g => W (g * h)) ∈ T
  psi : ∀ W ∈ T, ∀ x g, W (n2 x * g) = (ψ (-x) : ℂ) * W g
  cen : ∀ W ∈ T, ∀ (a : Fˣ) g, W (d2 a a * g) = ((ω a : ℂˣ) : ℂ) * W g
  smooth : ∀ W ∈ T, ∃ U : OpenSubgroup (GL (Fin 2) F), ∀ g, ∀ u ∈ U, W (g * u) = W g
  gauge : ∀ W ∈ T, ∃ (C B : ℝ) (N : ℕ), ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
    ‖W (d2 a 1 * k)‖ ≤ C / (modulus (a : F) : ℝ) ^ N ∧ (W (d2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)
  int : ∀ W ∈ T, ∀ χ, IsUnit1 χ → ∀ s : ℂ, 0 < s.re → s.re < 1 →
    Integrable (fun a => W (d2 a 1) * ((χ a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧
    Integrable (fun a => W (d2 a 1 * w2) * (((χ * ω)⁻¹ a : ℂˣ) : ℂ) * mp a (1 / 2 - s)) (multHaar F)
  fe : ∀ W ∈ T, ∀ χ, IsUnit1 χ → ∀ s : ℂ, 0 < s.re → s.re < 1 →
    ∫ a, W (d2 a 1 * w2) * (((χ * ω)⁻¹ a : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F =
      γ χ s * ∫ a, W (d2 a 1) * ((χ a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F

end Loc

def LocalFunctionalEquationGL3GL2 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν →
    ∀ (ω : Fˣ →* ℂˣ) (γ : (Fˣ →* ℂˣ) → ℂ → ℂ) (T : Submodule ℂ (GL (Fin 2) F → ℂ)), IsUnit1 ω → WhJL ψ ω γ T →
    ∀ W ∈ LFS.VF ψ (V2 ψ ν ν⁻¹), ∀ W' ∈ T, ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 →
      Integrable (z32 W W' s) (mu32 ψ) ∧ Integrable (z32 (dW3 W) (dW2 W') (1 - s)) (mu32 ψ) ∧
      ∫ p, z32 (dW3 W) (dW2 W') (1 - s) p ∂mu32 ψ = γ ν s * γ 1 s * γ ν⁻¹ s * ∫ p, z32 W W' s p ∂mu32 ψ

end Ad3.K.QuadraticBaseChangeGL3

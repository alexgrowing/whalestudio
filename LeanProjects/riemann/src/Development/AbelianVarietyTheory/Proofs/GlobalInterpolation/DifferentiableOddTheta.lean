import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber

open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.ThetaWeberRoad

def tpFactor (τ : ℍ) (z : ℂ) (n : ℕ) : ℂ :=
  (1 - cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ))) *
    (1 + cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) + 2 * π * I * z)) *
    (1 + cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) - 2 * π * I * z))

def TripleProduct : Prop := ∀ (τ : ℍ) (z : ℂ), HasProd (tpFactor τ z) (jacobiTheta₂ z τ)

def oddTheta (τ : ℍ) (z : ℂ) : ℂ :=
  cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) * jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ

theorem differentiable_oddTheta (τ : ℍ) : Differentiable ℂ (oddTheta τ) := by
  intro z
  have hexp : DifferentiableAt ℂ
      (fun w : ℂ => cexp (π * I * (τ : ℂ) / 4 + π * I * (w + 1 / 2))) z := by
    fun_prop
  have hshift : DifferentiableAt ℂ (fun w : ℂ => w + ((τ : ℂ) + 1) / 2) z :=
    differentiableAt_id.add_const _
  have htheta : DifferentiableAt ℂ
      (fun w : ℂ => jacobiTheta₂ (w + ((τ : ℂ) + 1) / 2) τ) z := by
    have h0 : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ w τ) (z + ((τ : ℂ) + 1) / 2) :=
      differentiableAt_jacobiTheta₂_fst _ τ.2
    exact h0.comp z hshift
  exact hexp.mul htheta

end GlobalTheory.ThetaWeberRoad

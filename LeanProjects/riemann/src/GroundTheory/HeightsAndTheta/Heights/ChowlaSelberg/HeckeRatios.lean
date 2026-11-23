import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm
open scoped Real

noncomputable section

def mulPoint (n : ℕ+) (τ : ℍ) : ℍ := (⟨(n : ℝ), by positivity⟩ : {x : ℝ // 0 < x}) • τ

def divPoint (n : ℕ+) (a : ℕ) (τ : ℍ) : ℍ :=
  (⟨(n : ℝ)⁻¹, by positivity⟩ : {x : ℝ // 0 < x}) • ((a : ℝ) +ᵥ τ)

theorem coe_mulPoint (n : ℕ+) (τ : ℍ) : (mulPoint n τ : ℂ) = (n : ℂ) * τ := by
  simp [mulPoint, coe_pos_real_smul, Complex.real_smul]

theorem coe_divPoint (n : ℕ+) (a : ℕ) (τ : ℍ) : (divPoint n a τ : ℂ) = ((a : ℂ) + τ) / n := by
  simp [divPoint, coe_pos_real_smul, coe_vadd, Complex.real_smul, div_eq_inv_mul]
  ring

def heckeRatios (n : ℕ+) (τ : ℍ) : Multiset ℂ :=
  ((n : ℂ) ^ 12 * discriminant (mulPoint n τ) / discriminant τ) ::ₘ
    (Multiset.range n).map fun a ↦ discriminant (divPoint n a τ) / discriminant τ

def HasIntegralLaurentQExpansion (f : ℍ → ℂ) : Prop :=
  ∃ (N : ℕ) (c : ℕ → ℤ) (A : ℝ), ∀ τ : ℍ, A < τ.im →
    HasSum (fun n ↦ (c n : ℂ) * Function.Periodic.qParam 1 τ ^ n)
      (Function.Periodic.qParam 1 τ ^ N * f τ)

theorem hasIntegralLaurentQExpansion_const (m : ℤ) :
    HasIntegralLaurentQExpansion fun _ ↦ (m : ℂ) := by
  refine ⟨0, fun n ↦ if n = 0 then m else 0, 0, fun τ _ ↦ ?_⟩
  convert hasSum_ite_eq 0 ((m : ℂ) * Function.Periodic.qParam 1 τ ^ 0) using 1
  · ext n; split_ifs <;> simp_all
  · simp

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg

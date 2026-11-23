import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve

open Complex Polynomial
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber

def thetaConst (a b : ℕ) (τ : ℍ) : ℂ :=
  cexp (π * I * (a : ℂ) ^ 2 * (τ : ℂ) / 4 + π * I * a * b / 2) *
    jacobiTheta₂ (((a : ℂ) * (τ : ℂ) + b) / 2) τ

def weberF (τ : ℍ) : ℂ :=
  cexp (-(π * I / 24)) * ModularForm.eta (((τ : ℂ) + 1) / 2) / ModularForm.eta τ

def weberF₁ (τ : ℍ) : ℂ := ModularForm.eta ((τ : ℂ) / 2) / ModularForm.eta τ

def weberF₂ (τ : ℍ) : ℂ := (√2 : ℝ) * ModularForm.eta (2 * (τ : ℂ)) / ModularForm.eta τ

def wp (τ : ℍ) (z : ℂ) : ℂ := (periodPairOfTau τ).weierstrassP z

def jLat (τ : ℍ) : ℂ := (latticeCurve (periodPairOfTau τ)).j

open Complex Polynomial in
open UpperHalfPlane hiding I in
open scoped Real in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.disc_ne_zero (τ : ℍ) :
    (_root_.GlobalTheory.periodPairOfTau τ).g₂ ^ 3 - 27 * (_root_.GlobalTheory.periodPairOfTau τ).g₃ ^ 2
      ≠ 0 := by
  rw [← _root_.GlobalTheory.latticeCurve_Δ]
  exact _root_.GlobalTheory.latticeCurve_Δ_ne_zero _

open Complex Polynomial in
open UpperHalfPlane hiding I in
open scoped Real in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.jLat_eq (τ : ℍ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.jLat τ = 1728 * (_root_.GlobalTheory.periodPairOfTau τ).g₂ ^ 3 /
    ((_root_.GlobalTheory.periodPairOfTau τ).g₂ ^ 3 -
      27 * (_root_.GlobalTheory.periodPairOfTau τ).g₃ ^ 2) := by
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.jLat, WeierstrassCurve.j, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ', _root_.GlobalTheory.latticeCurve_c₄,
    _root_.GlobalTheory.latticeCurve_Δ]
  ring

open Complex Polynomial in
open UpperHalfPlane hiding I in
open scoped Real in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.halfPeriods_notMem (τ : ℍ) :
    (1 / 2 : ℂ) ∉ (_root_.GlobalTheory.periodPairOfTau τ).lattice ∧
      (τ : ℂ) / 2 ∉ (_root_.GlobalTheory.periodPairOfTau τ).lattice ∧
      (1 + (τ : ℂ)) / 2 ∉ (_root_.GlobalTheory.periodPairOfTau τ).lattice := by
  have hpos := τ.im_pos
  refine ⟨?_, ?_, ?_⟩ <;> rw [_root_.GlobalTheory.mem_lattice_periodPairOfTau] <;>
    rintro ⟨m, n, h⟩ <;> have him := congrArg Complex.im h <;> have hre := congrArg Complex.re h <;>
    simp at him hre
  · rcases him with hm' | hm
    · subst hm'
      have h1 : (((2 * n - 1 : ℤ)) : ℝ) = 0 := by push_cast at hre ⊢; linarith
      have h2 : 2 * n - 1 = 0 := by exact_mod_cast h1
      omega
    · linarith
  · have h0 : (((2 * m - 1 : ℤ)) : ℝ) * τ.im = 0 := by push_cast; linarith
    rcases mul_eq_zero.1 h0 with hm | hm
    · have h2 : 2 * m - 1 = 0 := by exact_mod_cast hm
      omega
    · linarith
  · have h0 : (((2 * m - 1 : ℤ)) : ℝ) * τ.im = 0 := by push_cast; linarith
    rcases mul_eq_zero.1 h0 with hm | hm
    · have h2 : 2 * m - 1 = 0 := by exact_mod_cast hm
      omega
    · linarith

def HalfPeriodDiff (τ : ℍ) : Prop :=
  wp τ (1 / 2) - wp τ ((τ : ℂ) / 2) = (π : ℂ) ^ 2 * thetaConst 0 0 τ ^ 4 ∧
  wp τ (1 / 2) - wp τ ((1 + (τ : ℂ)) / 2) = (π : ℂ) ^ 2 * thetaConst 0 1 τ ^ 4 ∧
  wp τ ((1 + (τ : ℂ)) / 2) - wp τ ((τ : ℂ) / 2) = (π : ℂ) ^ 2 * thetaConst 1 0 τ ^ 4

def JacobiProduct (τ : ℍ) : Prop :=
  thetaConst 0 0 τ * thetaConst 0 1 τ * thetaConst 1 0 τ = 2 * ModularForm.eta τ ^ 3

def ThetaWeber (τ : ℍ) : Prop :=
  thetaConst 0 0 τ = ModularForm.eta τ * weberF τ ^ 2 ∧
  thetaConst 0 1 τ = ModularForm.eta τ * weberF₁ τ ^ 2 ∧
  thetaConst 1 0 τ = ModularForm.eta τ * weberF₂ τ ^ 2

def WeberCubic (τ : ℍ) : Prop :=
  ((X - C 16) ^ 3 - C (jLat τ) * X : ℂ[X]) =
    (X - C (weberF τ ^ 24)) * (X - C (-weberF₁ τ ^ 24)) * (X - C (-weberF₂ τ ^ 24))

def ThetaWeberStatement : Prop :=
  ∀ τ : ℍ, HalfPeriodDiff τ ∧ JacobiProduct τ ∧ ThetaWeber τ ∧ WeberCubic τ

open Complex Polynomial in
open UpperHalfPlane hiding I in
open scoped Real in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber.pow_twelve {τ : ℍ}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ / ModularForm.eta τ) ^ 12 = _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF τ ^ 24 ∧
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ / ModularForm.eta τ) ^ 12 = _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁ τ ^ 24 ∧
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ / ModularForm.eta τ) ^ 12 = _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂ τ ^ 24 := by
  have hη : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero τ.2
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, mul_div_cancel_left₀ _ hη, ← pow_mul]
  · rw [h2, mul_div_cancel_left₀ _ hη, ← pow_mul]
  · rw [h3, mul_div_cancel_left₀ _ hη, ← pow_mul]

example (τ : ℍ) : thetaConst 0 0 τ = jacobiTheta τ := by
  simp [thetaConst, jacobiTheta_eq_jacobiTheta₂]

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber

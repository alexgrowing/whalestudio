import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar
open scoped ComplexOrder

section Ball

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

def ballMat (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (τ : Ψ) : Matrix (Fin j) (Fin j') ℂ :=
  Matrix.of fun a b => t (q (τ, a, b))

def ballDom (q : Ψ × Fin j × Fin j' ≃ Fin n) : Set (Fin n → ℂ) :=
  {t | ∀ τ, (1 - (ballMat q t τ)ᴴ * ballMat q t τ).PosDef}

def ballPot (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ℝ :=
  -∑ τ, Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re

def ballDens (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ℝ := Real.exp ((j + j' : ℕ) * ballPot q t)

end Ball

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def autGrp (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) : Subgroup (Λ ≃ₗ[𝓞 E] Λ) where
  carrier := {γ | ∀ x y, form (γ x) (γ y) = form x y}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x y := by
    show form (a (b x)) (a (b y)) = form x y
    rw [ha, hb]
  inv_mem' {a} ha x y := by
    have h := ha (a.symm x) (a.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def RiemLat.HasSig {Ψ : Type} (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (j j' : ℕ) : Prop :=
  ∀ τ, Module.finrank ℂ (eigSp R.B (σ τ)) = j' ∧ Module.finrank ℂ (eigSp R.B ((starRingEnd ℂ).comp (σ τ))) = j

def RiemLat.EqvBy (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) : Prop :=
  ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, R'.P (γ x) = h (R.P x)

variable (E) in

structure UnivFam (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] where

  q : Ψ × Fin j × Fin j' ≃ Fin n

  σ : Ψ → (𝓞 E →+* ℂ)
  cm : IsCMFam σ

  form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ

  R : (Fin n → ℂ) → RiemLat E g Λ
  form_eq : ∀ t, (R t).form = form
  hol : IsHolFam (ballDom q) R
  sig : ∀ t ∈ ballDom q, (R t).HasSig σ j j'

  b : Ψ → Fin j' → (Fin n → ℂ) → Fin g → ℂ
  frames : IsEigFrames (ballDom q) (fun t => (R t).B) σ b
  logDet_eq : ∀ t ∈ ballDom q, (R t).logDet (fun τ i => b τ i t) = ballPot q t
  univ : ∀ R' : RiemLat E g Λ, R'.form = form → R'.HasSig σ j j' → ∃! t, t ∈ ballDom q ∧ (R t).EqvBy R' 1

namespace UnivFam

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (F : UnivFam E Ψ j j' n g Λ)

def Eqv (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (t t' : Fin n → ℂ) : Prop := ∃ γ ∈ Γ, (F.R t).EqvBy (F.R t') γ

def IsFundSet (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)) : Prop :=
  MeasurableSet FF ∧ FF ⊆ ballDom F.q ∧ (∀ t ∈ ballDom F.q, ∃ t' ∈ FF, F.Eqv Γ t t') ∧
    ∀ t ∈ FF, ∀ t' ∈ FF, F.Eqv Γ t t' → t = t'

def IsArith (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) : Prop := Γ ≤ autGrp F.form ∧ Γ.relIndex (autGrp F.form) ≠ 0

end UnivFam

end GlobalTheory.CompanionTheory.Ar.Cusp

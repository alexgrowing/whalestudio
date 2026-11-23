import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf

variable {D : D7}

def gramQ (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Matrix (Fin ρ) (Fin ρ) D.host.E :=
  xᴴ ⬝ (W.gram ⬝ x)

def Orb (W : HSp D) {ρ : ℕ} (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
  {x | LinearIndependent D.host.E x.transpose ∧ gramQ W x = gramQ W x₀}

def Rgrp (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) : Subgroup (GA D W) where
  carrier := {r | ∃ u ∈ UX D ρ, mt W r ⬝ x = x ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨v, hv, hb⟩
    exact ⟨u * v, mul_mem hu hv, by
      rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Units.val_mul, Matrix.mul_assoc]⟩
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h : mt W a⁻¹ ⬝ (x ⬝ u.1) = x := by rw [← ha, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    calc mt W a⁻¹ ⬝ x = mt W a⁻¹ ⬝ (x ⬝ u.1) ⬝ (u⁻¹).1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = x ⬝ (u⁻¹).1 := by rw [h]

section Source

variable (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (W : HSp D)

def Nfix (j : Fin ρ) : Subgroup (GA D V) :=
  flagN d ⊓ ⨅ i : {i : Fin ρ // i ≤ j}, fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)

def term (v : VolM D W.rank ρ) (Ψ : WO V W → ℂ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) : ℂ :=
  d.mixS W ψ v.μ v.𝓕 Ψ (rat x) 0

structure IsTh (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ) : Prop where
  cont : Continuous fun n : flagN d => Th n.1
  left : ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ n ∈ flagN d, Th (γ * n) = Th n
  cen : ∀ c, ∀ n ∈ flagN d, Th (d.nC c * n) = star (ψ (d.qS W c (rat x₀))) * Th n
  dep : ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → gramQ W x₀ *ᵥ a = 0 →
    ∃ (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V) (u : GA D V) (c : ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u ∧ u ∈ Nfix d j ∧ c ≠ 1 ∧
      ∀ n ∈ flagN d, ∀ n' ∈ flagN d, Th (n * u * n') = c * Th (n * n')

def IsBase (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Prop :=
  LinearIndependent D.host.E x₀.transpose ∧
    ∀ u ∈ UX D ρ, adj u.1 ⬝ ((rat (gramQ W x₀) : Mx D ρ ρ) ⬝ u.1) = rat (gramQ W x₀)

def flFun (v : VolM D W.rank ρ) (Th : GA D V → ℂ) (x : Mx D W.rank ρ) (Ψ : WO V W → ℂ) (u : UX D ρ)
    (b : Mx D ρ V₀.rank) : ℂ :=
  Th (d.nB b * d.levi u.1) * d.mixS W ψ v.μ v.𝓕 Ψ (x ⬝ u.1.1) (x ⬝ b)

def fl (v : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (Th : GA D V → ℂ) (x : Mx D W.rank ρ)
    (Ψ : WO V W → ℂ) : ℂ :=
  ∫ u, (∫ b in vb.𝓕, flFun ψ d W v Th x Ψ u b ∂vb.μ) ∂vU.ν

end Source

def kerBF {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) (φ : GA D B.A → ℂ)
    (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ) (h : GA D J.W) : ℂ :=
  G h * ∫ h₀ in B.vA.𝓕, φ h₀ * flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0 ∂B.vA.μ

end GlobalTheory.Unf

end

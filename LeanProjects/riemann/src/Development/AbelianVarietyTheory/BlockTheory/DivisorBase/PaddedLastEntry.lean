import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

def ph (y : ℝ) : ℝ := y * Real.log y - y

def size {a : ℕ} (nu : DomWeight a) : ℕ := ∑ i, (nu.w i).toNat

def lastEntry {a : ℕ} (nu : DomWeight a) : ℕ := nu.detShift.toNat

def padZero {a : ℕ} (b : ℕ) (nu : DomWeight a) (j : Fin b) : ℤ :=
  if h : j.1 < a then nu.w ⟨j.1, h⟩ else 0

def StepWeights {a b : ℕ} (lam nu : DomWeight a) (lam' : DomWeight b) : Prop :=
  (∀ i, 0 ≤ nu.w i) ∧ (∃ s' : ℤ, ∀ i, nu.w i = lam.w i + s') ∧
    ∃ s : ℤ, ∀ j, lam'.w j + s = padZero b nu j

def invNormSq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (P : VV ℂ lam) : ℝ :=
  (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) P P).re

def OpNormSqLe {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) : Prop :=
  ∀ P : VV ℂ lam, invNormSq lam' (T P) ≤ t * invNormSq lam P

def unitSq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) : ℝ :=
  ∑ τ, ∑ β, ∑ α, ‖(r τ : ℂ) * z τ β α‖ ^ 2

def tmax {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (nu : ι → DomWeight a) (S : ℝ) (Om : ι → ℝ) : ℝ :=
  S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ size (nu τ) * Real.exp 1 * (2 * (size (nu τ) : ℝ) + 2) ^ (2 * (a * b)) *
    Real.exp (∑ i, ph ((nu τ).w i : ℝ)))

def BlockBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b →
  ∀ (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b),
    (∀ τ, StepWeights (lam τ) (nu τ) (lam' τ)) →
    (a = b → ∀ τ, lastEntry (nu τ) = 0) →
  ∀ (r Om : ι → ℝ) (cD : ι → ℂ),
    (∀ τ, 0 < r τ) → (∀ τ, 0 < Om τ) → (∀ τ, ‖cD τ * (r τ : ℂ)‖ ^ 2 = 1 / Om τ) →
  ∀ (G : VCx ι a b → ℂ) (S : ℝ), Differentiable ℂ G →
    (∀ z, ‖G z‖ ≤ S * Real.exp (unitSq r z / 2)) →
    OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => lastEntry (nu τ)) (tmax b nu S Om)

example : ph 0 = 0 ∧ ph 1 = -1 := by simp [ph]

example : StepWeights (a := 1) (b := 2) ⟨fun _ => 0, fun _ _ _ => le_rfl⟩ ⟨fun _ => 3, fun _ _ _ => le_rfl⟩
    ⟨![2, -1], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩ := by
  refine ⟨fun _ => by norm_num, ⟨3, fun _ => by norm_num⟩, ⟨1, fun j => ?_⟩⟩
  fin_cases j <;> simp [padZero]

example {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) :
    ‖(fun _ : VCx ι a b => (1 : ℂ)) z‖ ≤ 1 * Real.exp (unitSq r z / 2) := by
  have h : 0 ≤ unitSq r z := by unfold unitSq; positivity
  simp only [norm_one, one_mul]
  exact Real.one_le_exp (by positivity)

end GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry

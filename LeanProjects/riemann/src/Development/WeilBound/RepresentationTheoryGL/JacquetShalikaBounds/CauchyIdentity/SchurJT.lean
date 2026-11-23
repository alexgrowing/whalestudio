import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldAlternant

noncomputable section

open Finset GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace PositivityTheory.RgJS

variable {m m' : ℕ}

def hN (p : ℕ) (α : Fin m → ℂ) : ℂ := ∑ k ∈ Finset.Nat.antidiagonalTuple m p, ∏ i, α i ^ k i

def hZ (z : ℤ) (α : Fin m → ℂ) : ℂ := if z < 0 then 0 else hN z.toNat α

def jt (α : Fin m → ℂ) (l : Fin m' → ℕ) : ℂ := (Matrix.of fun i j : Fin m' => hZ ((l j : ℤ) - j + i) α).det

def eEx (α : Fin m → ℂ) (i : Fin m) (r : ℕ) : ℂ := ∑ S ∈ (univ.erase i).powersetCard r, ∏ l ∈ S, α l

def altN (α : Fin m → ℂ) (μ : Fin m → ℕ) : ℂ := (Matrix.of fun i j => α i ^ μ j).det

def stair (m : ℕ) : Fin m → ℕ := fun j => m - 1 - j

def padN (m : ℕ) (l : Fin m' → ℕ) : Fin m → ℕ := fun i => if h : (i : ℕ) < m' then l ⟨i, h⟩ else 0

def cjt (m : ℕ) (A : ℝ) (l : Fin m' → ℕ) : ℝ :=
  (m'.factorial : ℝ) * ∏ j, (((l j + m' + 1 : ℕ) : ℝ) ^ m * A ^ l j * max A A⁻¹ ^ m')

def HGen : Prop := ∀ (m : ℕ) (α : Fin m → ℂ) (u : ℂ) (A : ℝ), 0 ≤ A → (∀ i, ‖α i‖ ≤ A) → A * ‖u‖ < 1 →
  HasSum (fun p => hN p α * u ^ p) (∏ i, (1 - α i * u)⁻¹) ∧ ∀ p, ‖hN p α‖ ≤ ((p + 1 : ℕ) : ℝ) ^ m * A ^ p

def ERel : Prop := ∀ (m : ℕ) (α : Fin m → ℂ) (i : Fin m) (p : ℕ),
  α i ^ p = ∑ r ∈ range m, (-1) ^ r * eEx α i r * hZ ((p : ℤ) - r) α

def AltJT : Prop := ∀ (m : ℕ) (α : Fin m → ℂ) (l : Fin m → ℕ), altN α (l + stair m) = altN α (stair m) * jt α l

def JTPad : Prop := ∀ (m m' : ℕ), m' ≤ m → ∀ (α : Fin m → ℂ) (l : Fin m' → ℕ), jt α (padN m l) = jt α l

def SchurJT : Prop := ∀ (m : ℕ) (z : Fin m → ℂˣ) (l : Fin m → ℕ),
  evalAt z (schur fun i => (l i : ℤ)) = jt (fun i => (z i : ℂ)) l

def SumBd : Prop := ∀ (m m' : ℕ) (A B ρ : ℝ), 0 < A → 0 < B → 0 ≤ ρ → ρ * A * B < 1 →
  Summable (fun l : {l : Fin m' → ℕ // Antitone l} => cjt m A l.1 * cjt m' B l.1 * ρ ^ (∑ j, l.1 j)) ∧
  ∀ (α : Fin m → ℂ), (∀ i, ‖α i‖ ≤ A) → ∀ l : Fin m' → ℕ, ‖jt α l‖ ≤ cjt m A l

def BetaGen : Prop := ∀ (m m' : ℕ) (α : Fin m → ℂ) (β : Fin m' → ℂˣ) (X : ℂ) (A B : ℝ), 0 < A → 0 < B →
  (∀ i, ‖α i‖ ≤ A) → (∀ j, ‖(β j : ℂ)‖ ≤ B) → ‖X‖ * A * B < 1 → Pairwise (fun j j' => (β j : ℂ) ≠ β j') →
  HasSum (fun l : {l : Fin m' → ℕ // Antitone l} => jt α l.1 * evalAt β (schur fun j => (l.1 j : ℤ)) * X ^ (∑ j, l.1 j))
    (∏ i, ∏ j, (1 - α i * β j * X)⁻¹)

def BetaAll : Prop := ∀ (m m' : ℕ) (α : Fin m → ℂ) (β : Fin m' → ℂˣ) (X : ℂ) (A B : ℝ), 0 < A → 0 < B →
  (∀ i, ‖α i‖ ≤ A) → (∀ j, ‖(β j : ℂ)‖ ≤ B) → ‖X‖ * A * B < 1 →
  HasSum (fun l : {l : Fin m' → ℕ // Antitone l} => jt α l.1 * evalAt β (schur fun j => (l.1 j : ℤ)) * X ^ (∑ j, l.1 j))
    (∏ i, ∏ j, (1 - α i * β j * X)⁻¹)

def Cauchy : Prop := ∀ (m m' : ℕ), m' ≤ m → ∀ (α : Fin m → ℂˣ) (β : Fin m' → ℂˣ) (X : ℂ) (A B : ℝ),
  (∀ i, ‖(α i : ℂ)‖ ≤ A) → (∀ j, ‖(β j : ℂ)‖ ≤ B) → ‖X‖ * A * B < 1 →
  Summable (fun l : {l : Fin m' → ℕ // Antitone l} =>
    ‖evalAt α (schur fun i => (padN m l.1 i : ℤ)) * evalAt β (schur fun j => (l.1 j : ℤ)) * X ^ (∑ j, l.1 j)‖) ∧
  HasSum (fun l : {l : Fin m' → ℕ // Antitone l} =>
    evalAt α (schur fun i => (padN m l.1 i : ℤ)) * evalAt β (schur fun j => (l.1 j : ℤ)) * X ^ (∑ j, l.1 j))
    (∏ i, ∏ j, (1 - (α i : ℂ) * β j * X)⁻¹)

end PositivityTheory.RgJS

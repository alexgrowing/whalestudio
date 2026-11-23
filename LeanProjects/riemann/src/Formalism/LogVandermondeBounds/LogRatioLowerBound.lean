import Mathlib

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def vandN (x : ℕ → ℝ) (N : ℕ) : ℝ := ∏ i ∈ range N, ∏ j ∈ Ico (i + 1) N, (x i - x j)

noncomputable def dimVN (x : ℕ → ℝ) (N : ℕ) : ℝ := vandN x N / ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ)

noncomputable def zetaR (M : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M

noncomputable def rowPar (k : ℕ) (v b : ℕ → ℝ) : ℕ → ℝ := fun i => if i < k - 1 then v i else - b (i - (k - 1))

def PlaceData (x Δ a B : ℝ) (k m : ℕ) (u v b w : ℕ → ℝ) : Prop :=
  (∀ i, i < k - 1 → 0 ≤ v i ∧ v i ≤ k * (4 * Δ)) ∧
  (∀ i, i + 1 < k - 1 → v i - v (i + 1) = 4 * Δ) ∧
  (∀ i, i < k - 1 → v i < u i ∧ u (i + 1) < v i) ∧
  (- b 0 < u (k - 1)) ∧
  ((u 0 ≤ 2 * a ∧ - a ≤ u (k - 1)) ∨
    (k * (4 * Δ) ≤ u 0 - v 0 ∧ u 0 - v 0 ≤ 2 * k * (4 * Δ) ∧ u (k - 1) = v (k - 2) - 1 / 2)) ∧
  (∀ j, j < m → b j < w j ∧ |w j - b j| ≤ b j / x) ∧
  (∀ j, j + 1 < m → w j < b (j + 1) ∧ 1 ≤ b (j + 1) - b j) ∧
  k * (4 * Δ) ≤ b 0 / x ∧ w (m - 1) ≤ 2 * B

def LogRatioLowerBound : Prop :=
  ∀ (ε C₀ : ℝ), 0 < ε → ε < 1 / 52 → 0 ≤ C₀ → ∃ C : ℝ, ∀ (x : ℝ), 1 ≤ x →
    let L := x ^ ε
    let B := Real.exp L
    let a := x * B
    ∀ (f m k : ℕ) (vE Δ g₁ g₂ : ℝ) (u v b w : ℕ → ℕ → ℝ)
      (Dstar dstar massk massr Isig Ipi : ℝ) (Lval : ℕ → ℝ),
    1 ≤ f → 1 ≤ m → 2 ≤ k → (k : ℝ) ≤ x ^ C₀ →
    Real.pi ≤ vE → Real.log vE ≤ L → 1 ≤ Δ → 1 ≤ g₁ → 1 ≤ g₂ →
    (∀ ρ, ρ < f → PlaceData x Δ a B k m (u ρ) (v ρ) (b ρ) (w ρ)) →
    0 < massk → 0 < massr → 0 < Isig → 0 < Ipi →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Lval M ∧ |Real.log (Lval M)| ≤ f * Real.log (zetaR M)) →
    (hmass : massr = massk * ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) →
    (hidx : ((2 : ℝ) ^ (2 * f))⁻¹ * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2) ≤ Isig / Ipi) →
    (hD : (2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m) ≤ Dstar) →
    (hd : dstar = massk * Ipi * ∏ ρ ∈ range f, dimVN (u ρ) k) →
    (∑ j ∈ range m, (1 / (f : ℝ)) * ∑ ρ ∈ range f, Real.log (w ρ j * vE / Real.pi))
        + m * (Real.log g₁ + Real.log g₂) - C * (L + (m : ℝ) ^ 2 * L / k)
      ≤ (1 / ((f : ℝ) * k)) * Real.log (Dstar / dstar)

end Formalism.LogVandermondeBounds.StandardLattice

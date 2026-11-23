import Mathlib

noncomputable section

open scoped NNReal

namespace GlobalTheory.EisGen

variable {G : Type} [TopologicalSpace G]

def LocReg (ht : G → ℝ≥0) (Ei : ℂ → G → ℂ) : Prop :=
  ∀ s₀ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → G → ℂ), 0 < r ∧
    (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Ei s g) ∧
    (∀ g, DifferentiableOn ℂ (fun s => H s g) (Metric.ball s₀ r)) ∧
    ContinuousOn (fun x : ℂ × G => H x.1 x.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ r, ∀ g, ‖H s g‖ ≤ C * (ht g : ℝ) ^ N

def ContFrom (ht : G → ℝ≥0) (σ₀ : ℝ) (e : ℂ → G → ℂ) : Prop :=
  ∃ Ei : ℂ → G → ℂ, (∀ s : ℂ, σ₀ < s.re → ∀ g, Ei s g = e s g) ∧ LocReg ht Ei

theorem ContFrom.mono {ht : G → ℝ≥0} {σ₀ σ₁ : ℝ} {e : ℂ → G → ℂ} (h : ContFrom ht σ₀ e) (hσ : σ₀ ≤ σ₁) : ContFrom ht σ₁ e :=
  let ⟨Ei, h1, h2⟩ := h
  ⟨Ei, fun s hs => h1 s (hσ.trans_lt hs), h2⟩

variable (E : Type) [Field E] (n : ℕ) in

def diagCols : Matrix (Fin (n + n)) (Fin n) E :=
  (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) E) (1 : Matrix (Fin n) (Fin n) E)).submatrix finSumFinEquiv.symm id

end GlobalTheory.EisGen

end

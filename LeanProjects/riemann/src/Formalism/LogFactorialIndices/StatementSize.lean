import Mathlib

noncomputable section

namespace Formalism.LatticeIndexTer

def ph (u : ℝ) : ℝ := u * Real.log u - u

def PhIncr : Prop :=
  ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → (1 ≤ u ∨ 1 ≤ v) → |ph (u + v) - ph u| ≤ v * Real.log (u + v + 2)

def PhIncrFalse : Prop :=
  ¬ ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → |ph (u + v) - ph u| ≤ v * Real.log (u + v + 2)

def PhIncrNat : Prop :=
  ∀ u v : ℕ, |ph ((u : ℝ) + v) - ph u| ≤ (v : ℝ) * Real.log ((u : ℝ) + v + 2)

def Interlaced (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S : ℝ) : Prop :=
  (∀ i, 0 ≤ c i ∧ c i ≤ S) ∧ ∀ i : Fin k, c' i ≤ c i.castSucc ∧ c i.succ ≤ c' i

def Interlace : Prop :=
  ∀ (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S w : ℝ), Interlaced k c c' S → 1 ≤ w →
    |(∑ i, ph (w + c i)) - ∑ i, ph (w + c' i)| ≤ (w + 2 * S) * Real.log (w + S + 2)

def InterlaceFalse : Prop :=
  ¬ ∀ (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S w : ℝ), Interlaced k c c' S → 0 ≤ w →
    |(∑ i, ph (w + c i)) - ∑ i, ph (w + c' i)| ≤ (w + 2 * S) * Real.log (w + S + 2)

def InterlaceNat : Prop :=
  ∀ (k : ℕ) (c : Fin (k + 1) → ℕ) (c' : Fin k → ℕ) (S w : ℕ),
    Interlaced k (fun i => (c i : ℝ)) (fun i => (c' i : ℝ)) S →
    |(∑ i, ph ((w : ℝ) + c i)) - ∑ i, ph ((w : ℝ) + c' i)| ≤
      ((w : ℝ) + 2 * S) * Real.log ((w : ℝ) + S + 2)

def hookProd (μ : YoungDiagram) : ℕ :=
  ∏ x ∈ μ.cells, ((μ.rowLen x.1 - x.2) + (μ.colLen x.2 - x.1) - 1)

def HookFact : Prop :=
  ∀ μ : YoungDiagram, ∏ i ∈ Finset.range (μ.colLen 0), (μ.rowLen i).factorial ≤ hookProd μ

def HookLog : Prop :=
  ∀ μ : YoungDiagram,
    (∑ i ∈ Finset.range (μ.colLen 0), Real.log ((μ.rowLen i).factorial : ℝ)) -
        ((μ.colLen 0 : ℝ) ^ 2) * Real.log ((μ.rowLen 0 : ℝ) + μ.colLen 0) ≤
      Real.log (hookProd μ : ℝ)

end Formalism.LatticeIndexTer

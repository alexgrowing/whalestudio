import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM

set_option autoImplicit false

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

def wAct {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    List (Fin n × Fin n) → Module.End ℂ M
  | [] => 1
  | p :: w => E p.1 p.2 * wAct E w

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def NE {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x : D) : ℝ :=
  ∑ l ∈ range (j + 1), ∑ w : Fin l → Fin n × Fin n, ‖((wAct E (List.ofFn w) x : D) : H)‖

def NT {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (f : Fin n → D) : ℝ :=
  ∑ c, NE E j (f c)

def dSW (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : List (Matrix (Fin n) (Fin n) ℂ) → H → H
  | [], v => v
  | X :: w, v => dS σ X (dSW σ w v)

def nuJ (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))) (v : H) : ℝ :=
  (Ws.map fun w => ‖dSW σ w v‖).sum

def DecBoundJ (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (m N : ℕ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))),
    (∀ w ∈ Ws, w.length ≤ N ∧ ∀ X ∈ w, inG ε X) ∧
    ∀ u v : H, IsSmoothVecU ε σ u → IsSmoothVecU ε σ v → ∀ g ∈ UJset ε,
      Real.sqrt (S7.hs g) ^ m * ‖inner ℂ v (σ g u)‖ ≤ C * nuJ σ Ws u * nuJ σ Ws v

end ReciprocityTheory.ChartRestriction.DS.DecInf

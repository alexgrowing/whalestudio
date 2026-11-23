import Mathlib

namespace Formalism.SL.MV

open Finset

noncomputable def kern {ι Mv : Type} [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (i j : ι) : ℝ :=
  ∑ m ∈ univ.filter (fun m => src m = i ∧ tgt m = j), μ m

def MoveKernel : Prop :=
  ∀ (ι Mv : Type) [Fintype ι] [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (inv : Mv → Mv),
    (∀ m, inv (inv m) = m) → (∀ m, src (inv m) = tgt m) → (∀ m, tgt (inv m) = src m) → (∀ m, μ (inv m) = μ m) →
    ∀ i j, kern src tgt μ i j = kern src tgt μ j i

def MoveBound : Prop :=
  ∀ (ι Mv : Type) [Fintype ι] [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (inv : Mv → Mv)
    (w : ι → ℂ) (χ : Mv → ℂ) (ε₁ ε₂ : ℝ),
    (∀ m, inv (inv m) = m) → (∀ m, src (inv m) = tgt m) → (∀ m, tgt (inv m) = src m) → (∀ m, μ (inv m) = μ m) →
    (∀ m, w (tgt m) = w (src m) * χ m) →
    (∀ i, ‖w i‖ ≤ 1) →
    (∀ i, |(∑ m ∈ univ.filter (fun m => src m = i), μ m) - 1| ≤ ε₁) →
    (∀ i, ‖∑ m ∈ univ.filter (fun m => src m = i), (μ m : ℂ) * χ m‖ ≤ ε₂) →
    ‖∑ i, w i‖ ≤ (ε₁ + ε₂) * (Fintype.card ι : ℝ)

end Formalism.SL.MV

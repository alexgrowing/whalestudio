import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul

noncomputable section
open Formalism.BasicNotions GlobalTheory.SeeSaw GlobalTheory.QPl
namespace GlobalTheory.QTw
variable {D : D7} {c : Comm D} {t : Tup c}

def resc (w : VTup t) (s : ∀ j, t.Ch j → ℂ) : VTup t :=
  { w with
    dQ := fun j α γ => (s j α * (s (j + 1) γ)⁻¹) • w.dQ j α γ
    ε := fun j α => s j α • w.ε j α
    εT := fun n h β => s n β • w.εT n h β }

def QPinU (v : VCom c) (w : VTup t) : Prop :=
  ∃ (w₀ : VTup t) (s : ∀ j, t.Ch j → ℂ), (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) ∧ QPin v w₀ ∧ w = resc w₀ s

theorem resc_one (w : VTup t) : resc w (fun _ _ => 1) = w := by
  simp [resc]

theorem QPinU.of {v : VCom c} {w : VTup t} (h : QPin v w) : QPinU v w :=
  ⟨w, fun _ _ => 1, fun _ _ => ⟨1, one_pos, one_pow 1⟩, h, (resc_one w).symm⟩

end GlobalTheory.QTw
end

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.Gauge

open GlobalTheory.TorsionForm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem wedge_smul {m : ℕ} (i : Fin m) (c : ℂ) (w : Ext m) : wedge i (c • w) = c • wedge i w := by
  funext S; by_cases hS : i ∈ S <;> simp [wedge, hS, mul_left_comm]

theorem contr_smul {m : ℕ} (i : Fin m) (c : ℂ) (w : Ext m) : contr i (c • w) = c • contr i w := by
  funext S; by_cases hS : i ∈ S <;> simp [contr, hS, mul_left_comm]

theorem wedge_add {m : ℕ} (i : Fin m) (v w : Ext m) : wedge i (v + w) = wedge i v + wedge i w := by
  funext S; by_cases hS : i ∈ S <;> simp [wedge, hS, mul_add]

theorem contr_add {m : ℕ} (i : Fin m) (v w : Ext m) : contr i (v + w) = contr i v + contr i w := by
  funext S; by_cases hS : i ∈ S <;> simp [contr, hS, mul_add]

theorem connForm_smul (τ : E → Matrix (Fin g) (Fin g) ℂ) (b v : E) (c : ℂ) (w : Ext (n + n + g)) :
    connForm τ b v (c • w) = c • connForm τ b v w := by
  simp only [connForm, contr_smul, wedge_smul, Finset.smul_sum, smul_comm c]

def commOp (τ : E → Matrix (Fin g) (Fin g) ℂ) (β : Fin n → E) (u : ℝ) (ρ : Pt E g → ℂ)
    (P : Pt E g) (w : Ext (n + n + g)) : Ext (n + n + g) :=
  ∑ i, (d10 ρ P (hor τ P (β i)) • wedge (dt g i) w + d01 ρ P (hor τ P (β i)) • wedge (dtb g i) w) +
    (Real.sqrt u : ℂ) • (∑ a, d01 ρ P (vert E a) • wedge (dzb n a) w -
      ∑ a, ∑ c, (2 * imPart τ P.1 a c * d10 ρ P (vert E a)) • contr (dzb n c) w)

end GlobalTheory.TorsionForm.Gauge

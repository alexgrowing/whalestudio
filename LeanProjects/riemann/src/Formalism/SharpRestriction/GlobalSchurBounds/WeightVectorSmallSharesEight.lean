import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesSeven

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

section Family

variable {eps : ℝ} (Fm : FamP eps)

def ChosenWall : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChW_at (Fm.Gx x i) Fm.GK

def Chosen8 (CH C0 C5 c6 : ℝ) : Prop :=
  ThickSetDensityEventually Fm ∧ ChosenTT Fm ∧ ChosenBadp Fm ∧ ChosenWall Fm ∧ ChosenQD Fm C5 ∧ ChosenThin Fm c6 ∧
    ChosenProviso Fm C0 ∧ ChosenCode Fm C0 CH

def WeightVectorSmallSharesEight (C0 CH : ℝ) : Prop := ∃ C5 c6 : ℝ, 0 < C5 ∧ 0 < c6 ∧ Chosen8 Fm CH C0 C5 c6

theorem chosenWS_of_wall (h : ChosenWall Fm) : ChosenWS Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨max x0 (Fm.x1 + 1), fun x hx hW => ?_⟩
  have hx1 : Fm.x1 < x := by
    have := le_of_max_le_right hx
    linarith
  have hxx : x ≥ x0 := le_of_max_le_left hx
  obtain ⟨i0⟩ := Fm.Ix_win x hW
  obtain ⟨a, b, hwin, hself⟩ := FamCore.coverU_hyp_self Fm.toFamCore x hx1 i0
  exact ⟨i0, a, b, hwin, ⟨i0, fun t => ⟨(hself t).1.symm, (hself t).2.symm⟩⟩, fun i _ => hx0 x hxx i⟩

end Family

end Formalism.MainNotions

end

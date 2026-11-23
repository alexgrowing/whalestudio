import Formalism.LocalToGlobal.HilbertRowConditions.RowPin

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

def LinkedFamiliesFixedSide : FamClass := fun {_} Fm =>
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Rows.SymmetricRowCompatibility (Fm.ex x hx i)

theorem LinkedFamiliesFixedSide.c2sk {eps : ℝ} {Fm : FamP eps} (h : LinkedFamiliesFixedSide Fm) : LinkedFamiliesKernelFrame Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx hx0 i => let ⟨T, _, _⟩ := h x hx hx0 i; ⟨T⟩⟩

theorem LinkedFamiliesFixedSide.c2s {eps : ℝ} {Fm : FamP eps} (h : LinkedFamiliesFixedSide Fm) : LinkedFamiliesLevelClass Fm := (LinkedFamiliesFixedSide.c2sk h).c2s

end Formalism.L2

end

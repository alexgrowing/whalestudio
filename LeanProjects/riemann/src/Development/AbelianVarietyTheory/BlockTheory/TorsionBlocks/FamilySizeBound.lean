import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FamilySizeBound

open Formalism.BasicNotions Formalism.MainNotions

def sizeAt (D : D7) (j : ℕ) (ρ : D.what₂.Tau) : ℝ := wj D (j + 1) ρ

def DataAt {D : D7} (L : SizeData₂ D) (C0 : ℝ) : Prop :=
  ∃ Δ : ℝ, StandardLattice.DataB D L.sc C0 Δ (sizeAt D)

def DataFam {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C0 x0 : ℝ, 0 < C0 ∧ ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, DataAt (Fm.L x i) C0

def Statement : Prop := ∀ (eps : ℝ) (Fm : FamP eps), DataFam Fm

end GlobalTheory.IndefiniteRowSideFullHecke.FamilySizeBound

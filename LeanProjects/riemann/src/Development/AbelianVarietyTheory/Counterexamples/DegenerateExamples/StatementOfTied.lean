import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.FamilyPartFiveOfExplicitConstants
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FamilySizeBound

noncomputable section

namespace GlobalTheory.DataRowsCounterexample

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke.FamilySizeBound

theorem places_nonempty (D : D7) : Nonempty D.what₂.Tau ∧ Nonempty D.what₂.Word :=
  ⟨⟨D.eTau.symm 1⟩, ⟨D.u₀⟩⟩

def FullFam {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C0 x0 : ℝ, 0 < C0 ∧ ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
    ∃ Δ : ℝ, StandardLattice.DataA (Fm.D x i) (Fm.L x i).sc C0 C0 Δ (sizeAt (Fm.D x i))

def Tied : Prop := ∃ (c : ℝ → ℝ) (x0 : ℝ), ∀ (eps : ℝ) (Fm : FamP eps), 0 < c Fm.CYL ∧
  ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, DataAt (Fm.L x i) (c Fm.CYL)

end GlobalTheory.DataRowsCounterexample

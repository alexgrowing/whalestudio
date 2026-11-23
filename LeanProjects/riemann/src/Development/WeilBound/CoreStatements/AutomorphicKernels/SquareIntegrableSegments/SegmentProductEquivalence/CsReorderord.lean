import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentProductEquivalence.ReorderCommon

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace PositivityTheory.PfEss.Zc2

theorem cs_reorderord : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (σ : Equiv.Perm (Fin h)) (y : Fin h → IrrGL k) (hd : ∑ a, (y a).1 = N) (hd' : ∑ a, (y (σ a)).1 = N), (∀ i j, i < j → ¬ (Γ i).Precedes (Γ j)) → (∀ i j, i < j → ¬ (Γ (σ i)).Precedes (Γ (σ j))) → (∀ i, IsLSeg (Γ i) (y i).rep) → Nonempty ((prodIrr y hd).Equiv (prodIrr (y ∘ σ) hd')) := by
  intro k _ _ _ _ _ hUC h N Γ σ y hd hd' hΓ hΓσ hseg
  have hnl : ∀ a b : Fin h, a < b → σ.symm b < σ.symm a → ¬(Γ a).Linked (Γ b) := by
    intro a b hab hba hl
    rcases Segment.linked_iff_precedes.mp hl with hp | hp
    · exact hΓ a b hab hp
    · have := hΓσ (σ.symm b) (σ.symm a) hba
      simp only [Equiv.apply_symm_apply] at this
      exact this hp
  exact reach_of_inv hUC hd hseg _ σ rfl hnl hd'

end PositivityTheory.PfEss.Zc2

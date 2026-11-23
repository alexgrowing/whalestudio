import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskyCosets.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContragredientProductIrreducibleImports
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.SquareIntegrableSegments.SegmentReordering.ReorderCommon

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace CompanionTheory.PfEss.Zc2

theorem cs_reorderord : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (σ : Equiv.Perm (Fin h)) (y : Fin h → IrrGL k) (hd : ∑ a, (y a).1 = N) (hd' : ∑ a, (y (σ a)).1 = N), (∀ i j, i < j → ¬ (Γ i).Precedes (Γ j)) → (∀ i j, i < j → ¬ (Γ (σ i)).Precedes (Γ (σ j))) → (∀ i, IsLSeg (Γ i) (y i).rep) → Nonempty ((prodIrr y hd).Equiv (prodIrr (y ∘ σ) hd')) := by
  intro k _ _ _ _ _ hcomm h N Γ σ y hd hd' h1 h2 hL
  refine reach_of_inv hcomm hd hL _ σ rfl ?_ hd'
  intro a b hab hinv hlk
  rcases Segment.linked_iff_precedes.1 hlk with hp | hp
  · exact h1 a b hab hp
  · have := h2 (σ.symm b) (σ.symm a) hinv
    simp only [Equiv.apply_symm_apply] at this
    exact this hp

end CompanionTheory.PfEss.Zc2

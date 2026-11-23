import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reverse_ordered_product_perm_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (σ : Equiv.Perm (Fin h)) (y : Fin h → IrrGL k) (hd : ∑ a, (y a).1 = N) (hd' : ∑ a, (y (σ a)).1 = N), IsRevOrdered Γ → IsRevOrdered (Γ ∘ σ) → (∀ i, IsLSeg (Γ i) (y i).rep) → Nonempty ((prodIrr y hd).Equiv (prodIrr (y ∘ σ) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered | exact GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered | (intros; apply GlobalTheory.CompanionTheory.ReorderRev.prodIrr_equiv_of_isRevOrdered <;> assumption)

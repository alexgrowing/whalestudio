import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalProductEquivMultiplicityOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_product_equiv_multiplicity_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL k) (hd : ∑ a, (y a).1 = N), IsCanon Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ (g : ℕ) (z : Fin g → IrrGL k) (hz : ∑ b, (z b).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr z hz)) ∧ jm z hz (prodIrr z hz) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.GroupCount.groupCount | exact GlobalTheory.CompanionTheory.GroupCount.groupCount | (intros; apply GlobalTheory.CompanionTheory.GroupCount.groupCount <;> assumption)

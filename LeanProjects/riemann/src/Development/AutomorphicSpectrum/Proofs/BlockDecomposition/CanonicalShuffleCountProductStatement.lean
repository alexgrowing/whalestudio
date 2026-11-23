import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalShuffleCountProduct
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_shuffle_count_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), IsCanon Γ → shuffleCount (List.ofFn fun i => decWord (Γ i)).flatten (fun i => decWord (Γ i)) = ∏ i, (Finset.univ.filter fun j => j ≤ i ∧ Γ j = Γ i).card := by
  first | exact @GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon | exact GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon | (intros; apply GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon <;> assumption)

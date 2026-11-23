import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackMemCuspFormSupLatticeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
open NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_mem_cuspFormSupLattice_iff : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)) (g : Y.V (wtZ a n)), Y.Pull f g → (g ∈ latW Y.U (wtZ a n) ↔ f ∈ latW (T.U j) (wtZ a n)) := by
  first | exact @GlobalTheory.CovTop.PullLat.pull_mem_latW | exact GlobalTheory.CovTop.PullLat.pull_mem_latW | (intros; apply GlobalTheory.CovTop.PullLat.pull_mem_latW <;> assumption)

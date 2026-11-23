import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumComplexCohomology
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.direct_sum_complex_cohomology : ∀ {K : Type} [Field K] {I : Type 1} [DecidableEq I] (E : I → Cx.{1} K) (n : ℕ), ∃ e : (⨁ i, (E i).H n) ≃ₗ[K] (Dsum E).H n, ∀ (i : I) (x : (E i).X n) (hx : (E i).d n x = 0) (hx' : (Dsum E).d n (DirectSum.lof K I (fun i => (E i).X n) i x) = 0), e (DirectSum.lof K I (fun i => (E i).H n) i ((E i).cls x hx)) = (Dsum E).cls (DirectSum.lof K I (fun i => (E i).X n) i x) hx' := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.dsum_coh | exact GlobalTheory.CompanionTheory.KunGlue.dsum_coh | (intros; apply GlobalTheory.CompanionTheory.KunGlue.dsum_coh <;> assumption)

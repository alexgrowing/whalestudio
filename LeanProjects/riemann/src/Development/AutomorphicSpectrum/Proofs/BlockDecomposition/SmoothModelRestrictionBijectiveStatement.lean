import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelRestrictionBijective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_model_restriction_bijective : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm → ∀ m j, Function.Bijective (resF l (B.schFn M.p) r.ρ m j) := by
  first | exact @GlobalTheory.CompanionTheory.FlatRes.flat_restriction | exact GlobalTheory.CompanionTheory.FlatRes.flat_restriction | (intros; apply GlobalTheory.CompanionTheory.FlatRes.flat_restriction <;> assumption)

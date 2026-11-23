import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatWittTowerLevel
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_witt_tower_level : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (m : ℕ), FlatL l m (Kt l F ρ m) := by
  first | exact @GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt | exact GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt | (intros; apply GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt <;> assumption)

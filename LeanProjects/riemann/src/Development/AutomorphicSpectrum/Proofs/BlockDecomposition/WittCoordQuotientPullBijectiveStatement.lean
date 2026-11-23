import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittCoordQuotientPullBijective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_coord_quotient_pull_bijective : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (cW : Coord q W d) (j : ℕ), Function.Bijective (((mqS q ρ hn {W}).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl)).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij | exact GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij | (intros; apply GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij <;> assumption)

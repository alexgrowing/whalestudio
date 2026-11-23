import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompareQuotientBijective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compare_quotient_bijective : ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) (l n i : ℕ), Function.Bijective ((cmpq A l n).f i) := by
  first | exact @GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective | exact GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective | (intros; apply GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective <;> assumption)

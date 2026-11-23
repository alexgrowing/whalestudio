import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdeal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_lifting_of_nil_ideal : ∀ {B : Type} [CommRing B] (J : Ideal B), (∀ x ∈ J, IsNilpotent x) → EtLift J := by
  first | exact @GlobalTheory.CompanionTheory.EtNil.etLift_of_nil | exact GlobalTheory.CompanionTheory.EtNil.etLift_of_nil | (intros; apply GlobalTheory.CompanionTheory.EtNil.etLift_of_nil <;> assumption)

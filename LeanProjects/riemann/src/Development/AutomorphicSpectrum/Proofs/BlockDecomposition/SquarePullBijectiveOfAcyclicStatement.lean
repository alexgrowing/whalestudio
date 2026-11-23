import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarePullBijectiveOfAcyclic
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_pull_bijective_of_acyclic : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) (ha : ∀ T, a.S T = ⊤),
    (∀ j, Subsingleton (CH.H (sq b (IdF.bot A)) j)) → ∀ j, Function.Bijective ((toSq a b ha).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective | exact GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective | (intros; apply GlobalTheory.CompanionTheory.LengthOneCochainExactness.pull_toSq_bijective <;> assumption)

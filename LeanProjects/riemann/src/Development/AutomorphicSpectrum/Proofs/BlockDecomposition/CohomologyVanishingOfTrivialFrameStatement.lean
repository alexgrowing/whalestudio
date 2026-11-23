import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingOfTrivialFrame
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishing_of_trivial_frame : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (E : Frame Φ 0) (F : C ⥤ ModuleCat.{0} R),
    Subsingleton (F.obj E.D) → ∀ n, Subsingleton (CH.H F n) := by
  first | exact @GlobalTheory.CompanionTheory.FramedSite.cohomology_subsingleton_of_frame_zero | exact GlobalTheory.CompanionTheory.FramedSite.cohomology_subsingleton_of_frame_zero | (intros; apply GlobalTheory.CompanionTheory.FramedSite.cohomology_subsingleton_of_frame_zero <;> assumption)

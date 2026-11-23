import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inOpen_of_thickening_morphism : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (V : X.Opens) {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T'), InU V T → InU V T' := by
  first | exact @GlobalTheory.CompanionTheory.ThickPt.inU_map | exact GlobalTheory.CompanionTheory.ThickPt.inU_map | (intros; apply GlobalTheory.CompanionTheory.ThickPt.inU_map <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_cocycle_class_independent : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ Λ' : CLiftK g D) (s : ℕ), (∀ c, (g.obj c).pdPow s = ⊥) → ∀ (hz : CH.d _ 2 (zK Λ s) = 0) (hz' : CH.d _ 2 (zK Λ' s) = 0), (CH.cx _).cls (zK Λ s) hz = (CH.cx _).cls (zK Λ' s) hz' := by
  first | exact @GlobalTheory.CompanionTheory.ConeZcls.main | exact GlobalTheory.CompanionTheory.ConeZcls.main | (intros; apply GlobalTheory.CompanionTheory.ConeZcls.main <;> assumption)

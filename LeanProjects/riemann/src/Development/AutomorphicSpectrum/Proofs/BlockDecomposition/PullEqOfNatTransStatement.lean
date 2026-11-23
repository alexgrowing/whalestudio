import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullEqOfNatTrans
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_eq_of_nat_trans : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) (m₁ m₂ : CH.Mor F F' (RingHom.id R)) (α : m₁.G ⟶ m₂.G), (∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x) → ∀ j, m₁.pull j = m₂.pull j := by
  first | exact @GlobalTheory.CompanionTheory.CatPrism.pull_eq_target | exact GlobalTheory.CompanionTheory.CatPrism.pull_eq_target | (intros; apply GlobalTheory.CompanionTheory.CatPrism.pull_eq_target <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatTransUpToSqPullback
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natTrans_upTo_sq_pullback : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F F' : C ⥤ ModuleCat.{w} R} (α : F ⟶ F') (s : R), (∀ T, UpTo s (α.app T).hom) → ∀ n, UpTo (s ^ 2) ((Mor.ofNatTrans α).pull n) := by
  first | exact @GlobalTheory.CompanionTheory.CoefUpTo.coef_upTo | exact GlobalTheory.CompanionTheory.CoefUpTo.coef_upTo | (intros; apply GlobalTheory.CompanionTheory.CoefUpTo.coef_upTo <;> assumption)

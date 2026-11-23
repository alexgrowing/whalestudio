import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ElementsBijectiveOfBijectiveApp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elements_bijective_of_bijective_app : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R), (∀ T, Function.Bijective (p.app T)) → ∀ n, Function.Bijective ((elMor p F).hom.f n) := by
  first | exact @GlobalTheory.CompanionTheory.Cech.elMor_bijective_of_bijective | exact GlobalTheory.CompanionTheory.Cech.elMor_bijective_of_bijective | (intros; apply GlobalTheory.CompanionTheory.Cech.elMor_bijective_of_bijective <;> assumption)

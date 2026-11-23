import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InitialObjectAugmentedResolution
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.initial_object_augmented_resolution : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (T₀ : C) (h : Limits.IsInitial T₀), (cx F).ResUpTo 1 (aug F fun T => (F.map (h.to T)).hom) := by
  first | exact @GlobalTheory.CompanionTheory.InitialCoh.resUpTo_one | exact GlobalTheory.CompanionTheory.InitialCoh.resUpTo_one | (intros; apply GlobalTheory.CompanionTheory.InitialCoh.resUpTo_one <;> assumption)

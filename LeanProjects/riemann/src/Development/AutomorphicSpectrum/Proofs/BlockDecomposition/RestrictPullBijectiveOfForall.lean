import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.OmRes

theorem restrict_pull_bijective_of_forall :
    ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
      (Q : ObjectProperty C), (∀ T, Q T) →
      ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict F Q.ι).pull n) := by
  intro R _ C _ F Q h n
  haveI : Q.ι.EssSurj := ⟨fun Y => ⟨⟨Y, h Y⟩, ⟨Iso.refl _⟩⟩⟩
  haveI : Q.ι.IsEquivalence := { }
  exact CrystallineSemistableComparison.P.adj F Q.ι Q.ι.inv Q.ι.asEquivalence.toAdjunction n

end GlobalTheory.CompanionTheory.OmRes

import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.MellinTransforms.Core1DOf
import GroundTheory.GlobalFields.IdeleGroups.Rational

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Global.RationalIdeles
open scoped NumberField.AdeleRing

namespace Ad3.GM.UnfoldingIntegralBis

abbrev Gam : Subgroup (IdeleGroup ℚ) := (IdeleGroup.diagonal ℚ).range

def gamEquiv : ℚˣ ≃ Gam := (MonoidHom.ofInjective (IdeleGroup.diagonal_injective ℚ)).toEquiv

instance countable_gam : Countable Gam := gamEquiv.surjective.countable

def iota (y : ℝ) : (InfiniteAdeleRing ℚ)ˣ :=
  IdeleGroup.toInfinite ℚ (moduleSection Rat.infinitePlace (expPos y))

def Rpos : Set (InfiniteAdeleRing ℚ)ˣ := {a | 0 < (realUnitsEquiv a : ℝ)}

end Ad3.GM.UnfoldingIntegralBis

import Mathlib
import Formalism.PeriodIntegrals.NormTransG
import Formalism.PeriodIntegrals.HeisNorm

open MeasureTheory

namespace PI.NormTransGW

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def phi (A : ℝ) (F : (T → I → J → ℂ) → ℂ) (z : T → I → J → ℂ) : ℝ :=
  ‖F z‖ ^ 2 * Real.exp (-Real.pi * (HfG A z z).re)

instance sigmaFinite_volume_single : SigmaFinite (volume : Measure (J → ℂ)) := inferInstance
instance addLeftInvariant_volume_single : (volume : Measure (J → ℂ)).IsAddLeftInvariant := inferInstance
instance sigmaFinite_volume_double : SigmaFinite (volume : Measure (I → J → ℂ)) := inferInstance
instance addLeftInvariant_volume_double : (volume : Measure (I → J → ℂ)).IsAddLeftInvariant := inferInstance
instance addLeftInvariant_volume_triple : (volume : Measure (T → I → J → ℂ)).IsAddLeftInvariant := inferInstance
instance vol_vinv : VAddInvariantMeasure (T → I → J → ℂ) (T → I → J → ℂ) volume := inferInstance
instance vol_vinvLat (La' : AddSubgroup (T → I → J → ℂ)) : VAddInvariantMeasure La' (T → I → J → ℂ) volume :=
  inferInstance

end PI.NormTransGW

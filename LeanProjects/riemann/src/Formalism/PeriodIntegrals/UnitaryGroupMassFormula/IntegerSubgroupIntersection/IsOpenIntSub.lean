import Mathlib
import Formalism.PeriodIntegrals.GaugeGap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInter

noncomputable section

namespace PI.GaugeCharW

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section

variable (F : Type) [Field F] [NumberField F]

def intSub : AddSubgroup (AF F) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F), sndA F x v ∈ v.adicCompletionIntegers F}
  add_mem' {a b} ha hb v := by
    rw [map_add]
    exact add_mem (ha v) (hb v)
  zero_mem' v := by
    rw [map_zero]
    exact zero_mem _
  neg_mem' {a} ha v := by
    rw [map_neg]
    exact neg_mem (ha v)

theorem isOpen_intSub (h3 : OpenInt) : IsOpen (intSub F : Set (AF F)) := by
  exact (h3 F).preimage (continuous_snd : Continuous (Prod.snd : Ainf F × Af F → Af F))

end

end PI.GaugeCharW

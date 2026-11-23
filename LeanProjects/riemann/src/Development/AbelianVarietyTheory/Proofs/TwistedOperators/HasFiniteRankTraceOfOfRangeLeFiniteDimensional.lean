import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets

namespace GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace

theorem hasFinTrace_of_range_le (X : Type) [AddCommGroup X] [Module ℂ X] (T : X →ₗ[ℂ] X)
    (Z : Submodule ℂ X) [FiniteDimensional ℂ Z] (hT : LinearMap.range T ≤ Z) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace T (LinearMap.trace ℂ Z (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x))) := by
  haveI : FiniteDimensional ℂ (LinearMap.range T) := Submodule.finiteDimensional_of_le hT
  refine ⟨inferInstance, ?_⟩
  have hmem : ∀ x : Z, (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x)) x ∈ (LinearMap.range T).comap Z.subtype :=
    fun x => LinearMap.mem_range_self T (x : X)
  rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hmem,
    ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hT)]
  congr 1

end GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace

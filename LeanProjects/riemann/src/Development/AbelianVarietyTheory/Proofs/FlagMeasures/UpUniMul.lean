import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.FormalDegreeBessel.FinalG

universe u_1

namespace GlobalTheory.UpperUnipotentProductFlagMeasures

theorem upUni_mul {R : Type u_1} [CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R}
    (h : Formalism.MainNotions.S.IsUpUni l) (h' : Formalism.MainNotions.S.IsUpUni l') : Formalism.MainNotions.S.IsUpUni (l * l') := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [(h i k).1 hk, zero_mul]
    · rw [(h' k j).1 (lt_of_lt_of_le hji hk), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(h i i).2 rfl, (h' i i).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [(h i k).1 hk, zero_mul]
      · rw [(h' k i).1 hk, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

end GlobalTheory.UpperUnipotentProductFlagMeasures
